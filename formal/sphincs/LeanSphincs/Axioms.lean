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
import LeanSphincs.LifetimeForecast
import LeanSphincs.LifetimeBank
import LeanSphincs.LifetimeFutureBank
import LeanSphincs.LifetimeIdealInterleaving
import LeanSphincs.LifetimeSources
import LeanSphincs.SecurityCacheMatch
import LeanSphincs.SecurityTargetAssignment
import LeanSphincs.SecurityPosition
import LeanSphincs.SecurityGraph
import LeanSphincs.SecurityPrefixExecution
import LeanSphincs.SecurityPrefixTrace
import LeanSphincs.SecurityPrefixFrontier
import LeanSphincs.SecurityPrefixSeparation
import LeanSphincs.SecurityPrefixPublic
import LeanSphincs.SecurityPrefixSigning
import LeanSphincs.SecurityPrefixSignLayer
import LeanSphincs.SecurityPrefixFullSign
import LeanSphincs.SecurityPreparedScheme
import LeanSphincs.LifetimeSourceSelection
import LeanSphincs.LifetimeGrindingCost
import LeanSphincs.SecurityMaterialGameCoupling
import LeanSphincs.SecurityGraphCache
import LeanSphincs.SecuritySurrogateAddress
import LeanSphincs.SecurityPrunedGraph
import LeanSphincs.LifetimeCachedSources
import LeanSphincs.LifetimeConditionalSources
import LeanSphincs.LifetimePairForecast
import LeanSphincs.LifetimePoolBalance
import LeanSphincs.SecurityPrefixCost
import LeanSphincs.SecurityPrefixCountedSign
import LeanSphincs.SecurityPrefixAllocation
import LeanSphincs.SecurityPrefixCostTransfer
import LeanSphincs.SecurityPrefixPrepared
import LeanSphincs.SecurityPrefixMaterialSampling
import LeanSphincs.SecuritySeedLoss
import LeanSphincs.LifetimeMarginal
import LeanSphincs.LifetimeSecondBank
import LeanSphincs.LifetimeJointBank
import LeanSphincs.LifetimeVarianceBudget
import LeanSphincs.LifetimeTransition
import LeanSphincs.LifetimePoolConcentration
import LeanSphincs.LifetimePoolRatio
import LeanSphincs.LifetimePoolGrinding
import LeanSphincs.SecurityGraphCorrectness
import LeanSphincs.SecurityPrefixMaterialView
import LeanSphincs.SecurityPrefixMaterialCost
import LeanSphincs.SecurityPrefixErasedKeygen
import LeanSphincs.LifetimePoolSigning
import LeanSphincs.LifetimeAdaptiveOccupancy
import LeanSphincs.LifetimePoolPreparation
import LeanSphincs.LifetimePoolOccupancy
import LeanSphincs.LifetimePairedOracle
import LeanSphincs.LifetimePairedMonitor
import LeanSphincs.LifetimeLocalizedGain
import LeanSphincs.SecurityHiddenReveal
import LeanSphincs.SecurityHiddenCharge
import LeanSphincs.SecurityExponentialCharge
import LeanSphincs.SecurityPrefixErasedGame
import LeanSphincs.SecurityGraphSampling
import LeanSphincs.LifetimeRectangles
import LeanSphincs.LifetimePriorMarginal
import LeanSphincs.LifetimeGainBudget
import LeanSphincs.LifetimeReserveBudget
import LeanSphincs.SecurityExponentialTrace
import LeanSphincs.LifetimePairedCharge
import LeanSphincs.LifetimePairedTrace
import LeanSphincs.LifetimePairedRectangles
import LeanSphincs.LifetimePairedBank
import LeanSphincs.LifetimePairedBankInclusion
import LeanSphincs.LifetimePairedReification
import LeanSphincs.SecurityHiddenRows
import LeanSphincs.SecurityHiddenGraph
import LeanSphincs.SecurityReferenceChoice
import LeanSphincs.LifetimeComparisonTransition
import LeanSphincs.LifetimeExcludedGain
import LeanSphincs.LifetimeGainCoordinates
import LeanSphincs.LifetimePairedPoolCoupling
import LeanSphincs.LifetimePairedAgreement
import LeanSphincs.LifetimePreparedSigning
import LeanSphincs.LifetimePreparedOccupancy
import LeanSphincs.LifetimeActualOccupancy
import LeanSphincs.LifetimeHybridOccupancy
import LeanSphincs.LifetimeHybridUnion
import LeanSphincs.SecurityEncodingPreparation
import LeanSphincs.SecurityReferenceSignature
import LeanSphincs.SecurityReferenceFailure
import LeanSphincs.SecurityHiddenWitness
import LeanSphincs.SecurityHiddenGraphRows
import LeanSphincs.SecurityHiddenGraphSampling
import LeanSphincs.SecurityGraphView
import LeanSphincs.SecurityGraphSigner
import LeanSphincs.LifetimeActiveBank
import LeanSphincs.LifetimeCenteredPairs
import LeanSphincs.LifetimeFullViewTrace
import LeanSphincs.LifetimeFutureOverflow
import LeanSphincs.LifetimePairEnergy
import LeanSphincs.LifetimePairProcess
import LeanSphincs.LifetimePairedSlots
import LeanSphincs.LifetimePairedWord
import LeanSphincs.LifetimePairedWordSupport
import LeanSphincs.LifetimeSmallQueryBudget
import LeanSphincs.LifetimeSourceProjection
import LeanSphincs.SecurityGraphCost
import LeanSphincs.SecurityGraphCountedSigner
import LeanSphincs.SecurityGraphCountedGame
import LeanSphincs.SecurityHiddenAccounting
import LeanSphincs.SecurityHiddenCost
import LeanSphincs.SecurityHiddenDeferred
import LeanSphincs.SecurityHiddenDomainAllocation
import LeanSphincs.SecurityHiddenMonitors
import LeanSphincs.SecurityHiddenOutside
import LeanSphincs.SecurityHiddenOutsideAccounting
import LeanSphincs.SecurityHiddenOutsideProgram
import LeanSphincs.SecurityHiddenStopping
import LeanSphincs.SecurityHiddenOutput
import LeanSphincs.BridgeReduce
import LeanSphincs.BridgeHiddenSample
import LeanSphincs.BridgeLazyGame
import LeanSphincs.BridgeSupport
import LeanSphincs.BridgeEncodingPrep
import LeanSphincs.BridgeFixedRun
import LeanSphincs.BridgeClassify
import LeanSphincs.BridgeImplication
import LeanSphincs.BridgeDebt
import LeanSphincs.BridgeSaturation

/-! Exact allowed-axiom guards for every public candidate theorem. -/

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

/-- info: 'LeanSphincs.Lifetime.blockForecast_some_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.blockForecast_some_left

/-- info: 'LeanSphincs.Lifetime.blockForecast_some_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.blockForecast_some_right

/-- info: 'LeanSphincs.Lifetime.blockForecast_both' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.blockForecast_both

/-- info: 'LeanSphincs.Lifetime.blockForecast_reveal_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.blockForecast_reveal_left

/-- info: 'LeanSphincs.Lifetime.blockForecast_reveal_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.blockForecast_reveal_right

/-- info: 'LeanSphincs.Lifetime.candidateInput_candidate_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.candidateInput_candidate_injective

/-- info: 'LeanSphincs.Lifetime.digestForecast_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.digestForecast_fresh

/-- info: 'LeanSphincs.Lifetime.expected_digestForecast_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_digestForecast_query

/-- info: 'LeanSphincs.Lifetime.digestForecast_eq_expected_messageDigest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.digestForecast_eq_expected_messageDigest

/-- info: 'LeanSphincs.Lifetime.fresh_digestForecast_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fresh_digestForecast_uniform

/-- info: 'LeanSphincs.Lifetime.expected_digestBankValue_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_digestBankValue_query

/-- info: 'LeanSphincs.Lifetime.query_other_cache_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.query_other_cache_eq

/-- info: 'LeanSphincs.Lifetime.digestBankStep_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.digestBankStep_preserves

/-- info: 'LeanSphincs.Lifetime.expected_digestBankStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_digestBankStep

/-- info: 'LeanSphincs.Lifetime.expected_digestBankStep_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_digestBankStep_le

/-- info: 'LeanSphincs.Lifetime.expected_adaptiveDigestBank_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_adaptiveDigestBank_le

/-- info: 'LeanSphincs.Lifetime.digestForecast_average' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.digestForecast_average

/-- info: 'LeanSphincs.Lifetime.uniformDigestForecast_average' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.uniformDigestForecast_average

/-- info: 'LeanSphincs.Lifetime.digestBankValue_average' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.digestBankValue_average

/-- info: 'LeanSphincs.Lifetime.futureCoverWeight_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.futureCoverWeight_zero

/-- info: 'LeanSphincs.Lifetime.futureCoverWeight_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.futureCoverWeight_succ

/-- info: 'LeanSphincs.Lifetime.initial_futureCoverWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.initial_futureCoverWeight

/-- info: 'LeanSphincs.Lifetime.futureBankPotential_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.futureBankPotential_query

/-- info: 'LeanSphincs.Lifetime.futureBankPotential_disclosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.futureBankPotential_disclosure

/-- info: 'LeanSphincs.Lifetime.initial_futureBankPotential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.initial_futureBankPotential

/-- info: 'LeanSphincs.Lifetime.covered_candidate_le_futureBankPotential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.covered_candidate_le_futureBankPotential

/-- info: 'LeanSphincs.Lifetime.expected_bind_le_of_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_bind_le_of_support

/-- info: 'LeanSphincs.Lifetime.expected_bind_le_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_bind_le_constant

/-- info: 'LeanSphincs.Lifetime.expected_idealInterleavedBank_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_idealInterleavedBank_le

/-- info: 'LeanSphincs.Lifetime.probEvent_idealInterleavedBank_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_idealInterleavedBank_le

/-- info: 'LeanSphincs.Lifetime.ideal_interleaving_lifetime_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.ideal_interleaving_lifetime_bound

/-- info: 'LeanSphincs.Lifetime.ideal_interleaving_after_keygen_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.ideal_interleaving_after_keygen_bound

/-- info: 'LeanSphincs.Lifetime.idealInterleavingLifetimeBound_of_fors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.idealInterleavingLifetimeBound_of_fors

/-- info: 'LeanSphincs.Lifetime.requested_ideal_interleaving_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.requested_ideal_interleaving_bounds

/-- info: 'LeanSphincs.Lifetime.CachedSource.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.CachedSource.mono

/-- info: 'LeanSphincs.Lifetime.CachedSource.unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.CachedSource.unique

/-- info: 'LeanSphincs.Lifetime.messageDigest_support_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.messageDigest_support_source

/-- info: 'LeanSphincs.Lifetime.sourcesConsistent_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.sourcesConsistent_mono

/-- info: 'LeanSphincs.Lifetime.sourcedPrior_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.sourcedPrior_cons

/-- info: 'LeanSphincs.Lifetime.signWithSources_forget_sources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.signWithSources_forget_sources

/-- info: 'LeanSphincs.Lifetime.signWithSources_forget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.signWithSources_forget

/-- info: 'LeanSphincs.Lifetime.finishSignBody_support_randomness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.finishSignBody_support_randomness

/-- info: 'LeanSphincs.Lifetime.signWithSources_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.signWithSources_preserves

/-- info: 'LeanSphincs.Lifetime.sources_same_pair_same_digest' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.sources_same_pair_same_digest

/-- info: 'LeanSphincs.Lifetime.sourcedPrior_duplicate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.sourcedPrior_duplicate

/-- info: 'LeanSphincs.Lifetime.signWithSources_record_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.signWithSources_record_shape

/-- info: 'LeanSphincs.Lifetime.signWithSources_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.signWithSources_logged

/-- info: 'LeanSphincs.Lifetime.sourceExcludedViews_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.sourceExcludedViews_subset

/-- info: 'LeanSphincs.Lifetime.successfulViews_subset_sourcedPrior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.successfulViews_subset_sourcedPrior

/-- info: 'LeanSphincs.Lifetime.sourceExcludedViews_eq_of_no_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.sourceExcludedViews_eq_of_no_success

/-- info: 'LeanSphincs.Lifetime.sourceExcludedViews_same_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.sourceExcludedViews_same_source

/-- info: 'LeanSphincs.Lifetime.successfulSource_logged' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.successfulSource_logged

/-- info: 'LeanSphincs.Security.CacheMatch.bad_cacheQuery_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.CacheMatch.bad_cacheQuery_iff

/-- info: 'LeanSphincs.Security.CacheMatch.probEvent_hash_query_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.CacheMatch.probEvent_hash_query_le

/-- info: 'LeanSphincs.Security.CacheMatch.expected_potential_eq_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.CacheMatch.expected_potential_eq_event

/-- info: 'LeanSphincs.Security.CacheMatch.expected_query_potential_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.CacheMatch.expected_query_potential_le

/-- info: 'LeanSphincs.Security.CacheMatch.counted_program_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.CacheMatch.counted_program_bound

/-- info: 'LeanSphincs.Security.TargetAssignment.atFields_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.TargetAssignment.atFields_unique

/-- info: 'LeanSphincs.Security.TargetAssignment.parseFields_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.TargetAssignment.parseFields_some_iff

/-- info: 'LeanSphincs.Security.TargetAssignment.parseFields_tweakable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.TargetAssignment.parseFields_tweakable

/-- info: 'LeanSphincs.Security.TargetAssignment.targets_card_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.TargetAssignment.targets_card_le_one

/-- info: 'LeanSphincs.Security.TargetAssignment.targets_at_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.TargetAssignment.targets_at_entry

/-- info: 'LeanSphincs.Security.TargetAssignment.canonical_input_excluded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.TargetAssignment.canonical_input_excluded

/-- info: 'LeanSphincs.Security.TargetAssignment.distinct_match_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.TargetAssignment.distinct_match_bad

/-- info: 'LeanSphincs.Security.TargetAssignment.surrogate_match_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.TargetAssignment.surrogate_match_bad

/-- info: 'LeanSphincs.Security.TargetAssignment.counted_structural_target_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.TargetAssignment.counted_structural_target_bound

/-- info: 'LeanSphincs.Security.hashFields_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.hashFields_injective

/-- info: 'LeanSphincs.Security.Position.domain_inRange' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Position.domain_inRange

/-- info: 'LeanSphincs.Security.Position.domain_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Position.domain_injective

/-- info: 'LeanSphincs.Security.Position.children_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Position.children_length_le

/-- info: 'LeanSphincs.Security.Position.depth_lt_of_mem_children' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Position.depth_lt_of_mem_children

/-- info: 'LeanSphincs.Security.Position.fields_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Position.fields_injective

/-- info: 'LeanSphincs.Security.Position.input_separated' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Position.input_separated

/-- info: 'LeanSphincs.Security.Graph.canonicalGraphInput_separated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.canonicalGraphInput_separated

/-- info: 'LeanSphincs.Security.Graph.canonicalGraphInput_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.canonicalGraphInput_congr

/-- info: 'LeanSphincs.Security.Graph.readCanonicalGraph_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.readCanonicalGraph_preserves

/-- info: 'LeanSphincs.Security.Graph.readCanonicalGraph_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.readCanonicalGraph_consistent

/-- info: 'LeanSphincs.Security.Graph.graphOrder_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.graphOrder_nodup

/-- info: 'LeanSphincs.Security.Graph.mem_graphOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.mem_graphOrder

/-- info: 'LeanSphincs.Security.Graph.graphOrder_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.graphOrder_sorted

/-- info: 'LeanSphincs.Security.Graph.eval_prepare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.eval_prepare

/-- info: 'LeanSphincs.Security.Graph.input_read_above' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.input_read_above

/-- info: 'LeanSphincs.Security.Graph.prepare_queriedInputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.prepare_queriedInputs

/-- info: 'LeanSphincs.Security.Prefix.splitWorld_hash_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.splitWorld_hash_step

/-- info: 'LeanSphincs.Security.Prefix.splitWorld_sample_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.splitWorld_sample_step

/-- info: 'LeanSphincs.Security.Prefix.splitWorld_hash_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.splitWorld_hash_bound

/-- info: 'LeanSphincs.Security.Prefix.splitWorld_prefix_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.splitWorld_prefix_bound

/-- info: 'LeanSphincs.Security.Prefix.fixedImpl_splitWorld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.fixedImpl_splitWorld

/-- info: 'LeanSphincs.Security.Prefix.simulate_splitWorld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.simulate_splitWorld

/-- info: 'LeanSphincs.Security.Prefix.tableWorld_fixedHashWorld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.tableWorld_fixedHashWorld

/-- info: 'LeanSphincs.Security.Prefix.realRun_byte_distribution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.realRun_byte_distribution

/-- info: 'LeanSphincs.Security.Prefix.counted_splitWorld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.counted_splitWorld

/-- info: 'LeanSphincs.Security.Prefix.splitWorld_twoEdge_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.splitWorld_twoEdge_bound

/-- info: 'LeanSphincs.Security.Prefix.observedTrace_covers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.observedTrace_covers

/-- info: 'LeanSphincs.Security.Prefix.twoEdgeEvent_of_covers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.twoEdgeEvent_of_covers

/-- info: 'LeanSphincs.Security.Prefix.twoEdgeEvent_observedTrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.twoEdgeEvent_observedTrace

/-- info: 'LeanSphincs.Security.Prefix.parse_later_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.parse_later_chain

/-- info: 'LeanSphincs.Security.Prefix.avoids_chainWalk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.avoids_chainWalk

/-- info: 'LeanSphincs.Security.Prefix.chainWalk_above_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.chainWalk_above_answer

/-- info: 'LeanSphincs.Security.Prefix.disclosed_value_from_frontier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.disclosed_value_from_frontier

/-- info: 'LeanSphincs.Security.Prefix.endpoint_from_frontier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.endpoint_from_frontier

/-- info: 'LeanSphincs.Security.Prefix.chainInput_address' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.chainInput_address

/-- info: 'LeanSphincs.Security.Prefix.parse_other_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.parse_other_chain

/-- info: 'LeanSphincs.Security.Prefix.parse_other_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.parse_other_domain

/-- info: 'LeanSphincs.Security.Prefix.parse_derive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.parse_derive

/-- info: 'LeanSphincs.Security.Prefix.eval_derive_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.eval_derive_answer

/-- info: 'LeanSphincs.Security.Prefix.eval_other_hash_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.eval_other_hash_answer

/-- info: 'LeanSphincs.Security.Prefix.eval_other_chain_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.eval_other_chain_answer

/-- info: 'LeanSphincs.Security.Prefix.publicEndpoints_replaceSecret' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.publicEndpoints_replaceSecret

/-- info: 'LeanSphincs.Security.Prefix.oneTimePublicKey_from_frontier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.oneTimePublicKey_from_frontier

/-- info: 'LeanSphincs.Security.Prefix.publicNode_replaceSecret' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.publicNode_replaceSecret

/-- info: 'LeanSphincs.Security.Prefix.treeNode_from_frontier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.treeNode_from_frontier

/-- info: 'LeanSphincs.Security.Prefix.surrogate_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.surrogate_answer

/-- info: 'LeanSphincs.Security.Prefix.publicSpine_replaceSecret' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.publicSpine_replaceSecret

/-- info: 'LeanSphincs.Security.Prefix.spineNode_from_frontier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.spineNode_from_frontier

/-- info: 'LeanSphincs.Security.Prefix.treeRoot_from_frontier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.treeRoot_from_frontier

/-- info: 'LeanSphincs.Security.Prefix.publicPath_replaceSecret' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.publicPath_replaceSecret

/-- info: 'LeanSphincs.Security.Prefix.treePath_from_frontier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.treePath_from_frontier

/-- info: 'LeanSphincs.Security.Prefix.encode_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.encode_answer

/-- info: 'LeanSphincs.Security.Prefix.firstEncoding_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.firstEncoding_answer

/-- info: 'LeanSphincs.Security.Prefix.otsSignFrom_eq_firstEncoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.otsSignFrom_eq_firstEncoding

/-- info: 'LeanSphincs.Security.Prefix.publicValues_replaceSecret' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.publicValues_replaceSecret

/-- info: 'LeanSphincs.Security.Prefix.signing_values_from_frontier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.signing_values_from_frontier

/-- info: 'LeanSphincs.Security.Prefix.otsSignFrom_from_frontier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.otsSignFrom_from_frontier

/-- info: 'LeanSphincs.Security.Prefix.ftsNode_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.ftsNode_answer

/-- info: 'LeanSphincs.Security.Prefix.ftsKey_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.ftsKey_answer

/-- info: 'LeanSphincs.Security.Prefix.ftsOpen_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.ftsOpen_answer

/-- info: 'LeanSphincs.Security.Prefix.publicLayer_replaceSecret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.publicLayer_replaceSecret

/-- info: 'LeanSphincs.Security.Prefix.signLayer_from_frontier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.signLayer_from_frontier

/-- info: 'LeanSphincs.Security.Prefix.referenceCutoff_of_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.referenceCutoff_of_selected

/-- info: 'LeanSphincs.Security.Prefix.referenceCutoff_of_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.referenceCutoff_of_none

/-- info: 'LeanSphincs.Security.Prefix.referenceCutoff_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.referenceCutoff_safe

/-- info: 'LeanSphincs.Security.Prefix.signLayer_from_referenceCutoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.signLayer_from_referenceCutoff

/-- info: 'LeanSphincs.Security.Prefix.messageDigestCall_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.messageDigestCall_answer

/-- info: 'LeanSphincs.Security.Prefix.messageDigest_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.messageDigest_answer

/-- info: 'LeanSphincs.Security.Prefix.fixedHashWorld_lift_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.fixedHashWorld_lift_hash

/-- info: 'LeanSphincs.Security.Prefix.fixedHashWorld_lift_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.fixedHashWorld_lift_prob

/-- info: 'LeanSphincs.Security.Prefix.signAttempt_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.signAttempt_answer

/-- info: 'LeanSphincs.Security.Prefix.signDigestLoop_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.signDigestLoop_answer

/-- info: 'LeanSphincs.Security.Prefix.publicFinishSign_replaceSecret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.publicFinishSign_replaceSecret

/-- info: 'LeanSphincs.Security.Prefix.finishSign_from_referenceCutoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.finishSign_from_referenceCutoff

/-- info: 'LeanSphincs.Security.Prefix.publicSign_replaceSecret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.publicSign_replaceSecret

/-- info: 'LeanSphincs.Security.Prefix.sign_from_referenceCutoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.sign_from_referenceCutoff

/-- info: 'LeanSphincs.Security.PreparedScheme.simulate_sequenceFin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.simulate_sequenceFin

/-- info: 'LeanSphincs.Security.PreparedScheme.compile_oracleHash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.compile_oracleHash

/-- info: 'LeanSphincs.Security.PreparedScheme.compile_parameter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.compile_parameter

/-- info: 'LeanSphincs.Security.PreparedScheme.compile_secret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.compile_secret

/-- info: 'LeanSphincs.Security.PreparedScheme.compile_ots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.compile_ots

/-- info: 'LeanSphincs.Security.PreparedScheme.compile_fts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.compile_fts

/-- info: 'LeanSphincs.Security.PreparedScheme.compile_surrogate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.compile_surrogate

/-- info: 'LeanSphincs.Security.PreparedScheme.compile_tweakableHash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.compile_tweakableHash

/-- info: 'LeanSphincs.Security.PreparedScheme.compile_messageDigestCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.compile_messageDigestCall

/-- info: 'LeanSphincs.Security.PreparedScheme.compileWorld_lift_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.compileWorld_lift_hash

/-- info: 'LeanSphincs.Security.PreparedScheme.compileWorld_lift_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.compileWorld_lift_prob

/-- info: 'LeanSphincs.Security.PreparedScheme.compile_chainWalk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.compile_chainWalk

/-- info: 'LeanSphincs.Security.PreparedScheme.compile_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.compile_encode

/-- info: 'LeanSphincs.Security.PreparedScheme.compiled_oneTimePublicKey_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.compiled_oneTimePublicKey_eq

/-- info: 'LeanSphincs.Security.PreparedScheme.compiled_treeNode_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.compiled_treeNode_eq

/-- info: 'LeanSphincs.Security.PreparedScheme.compiled_surrogate_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.compiled_surrogate_eq

/-- info: 'LeanSphincs.Security.PreparedScheme.compiled_spineNode_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.compiled_spineNode_eq

/-- info: 'LeanSphincs.Security.PreparedScheme.compiled_treePath_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.compiled_treePath_eq

/-- info: 'LeanSphincs.Security.PreparedScheme.compiled_ftsNode_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.compiled_ftsNode_eq

/-- info: 'LeanSphincs.Security.PreparedScheme.compiled_ftsKey_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.compiled_ftsKey_eq

/-- info: 'LeanSphincs.Security.PreparedScheme.compiled_ftsOpen_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.compiled_ftsOpen_eq

/-- info: 'LeanSphincs.Security.PreparedScheme.compiled_otsSignFrom_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.compiled_otsSignFrom_eq

/-- info: 'LeanSphincs.Security.PreparedScheme.compiled_keygen_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.compiled_keygen_eq

/-- info: 'LeanSphincs.Security.PreparedScheme.compile_keygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.compile_keygen

/-- info: 'LeanSphincs.Security.PreparedScheme.compiled_signLayer_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.compiled_signLayer_eq

/-- info: 'LeanSphincs.Security.PreparedScheme.compile_messageDigest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.compile_messageDigest

/-- info: 'LeanSphincs.Security.PreparedScheme.compiled_finishSign_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.compiled_finishSign_eq

/-- info: 'LeanSphincs.Security.PreparedScheme.compile_signAttempt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.compile_signAttempt

/-- info: 'LeanSphincs.Security.PreparedScheme.compiled_signDigestLoop_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.compiled_signDigestLoop_eq

/-- info: 'LeanSphincs.Security.PreparedScheme.compiled_sign_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.compiled_sign_eq

/-- info: 'LeanSphincs.Security.PreparedScheme.compile_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.compile_sign

/-- info: 'LeanSphincs.Security.PreparedScheme.compile_sign_of_keyRel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.compile_sign_of_keyRel

/-- info: 'LeanSphincs.Security.PreparedScheme.programCache_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.programCache_lookup

/-- info: 'LeanSphincs.Security.PreparedScheme.programCache_cacheQuery_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.programCache_cacheQuery_none

/-- info: 'LeanSphincs.Security.PreparedScheme.simulate_tick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.simulate_tick

/-- info: 'LeanSphincs.Security.PreparedScheme.simulate_ordinary_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.simulate_ordinary_query

/-- info: 'LeanSphincs.Security.PreparedScheme.run_compileHash_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.run_compileHash_query

/-- info: 'LeanSphincs.Security.PreparedScheme.run_compileHash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.run_compileHash

/-- info: 'LeanSphincs.Security.PreparedScheme.preparedRom_lift_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.preparedRom_lift_hash

/-- info: 'LeanSphincs.Security.PreparedScheme.run_compileWorld_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.run_compileWorld_query

/-- info: 'LeanSphincs.Security.PreparedScheme.run_compileWorld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.run_compileWorld

/-- info: 'LeanSphincs.Security.PreparedScheme.counted_query' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.counted_query

/-- info: 'LeanSphincs.Security.PreparedScheme.countPrepared_compileWorld_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.countPrepared_compileWorld_query

/-- info: 'LeanSphincs.Security.PreparedScheme.countPrepared_compileWorld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.countPrepared_compileWorld

/-- info: 'LeanSphincs.Security.PreparedScheme.simulateQ_countPreparedQueries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.simulateQ_countPreparedQueries

/-- info: 'LeanSphincs.Security.PreparedScheme.run_compileWorld_counted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.run_compileWorld_counted

/-- info: 'LeanSphincs.Security.PreparedScheme.run'_compileWorld_counted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.run'_compileWorld_counted

/-- info: 'LeanSphincs.Security.PreparedScheme.run_sign_counted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.run_sign_counted

/-- info: 'LeanSphincs.Security.PreparedScheme.keygen_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.keygen_eq

/-- info: 'LeanSphincs.Security.PreparedScheme.run_keygen_counted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.run_keygen_counted

/-- info: 'LeanSphincs.Security.PreparedScheme.run_ordinaryWorld_query_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PreparedScheme.run_ordinaryWorld_query_outside

/-- info: 'LeanSphincs.Lifetime.randomizerAverage_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.randomizerAverage_card

/-- info: 'LeanSphincs.Lifetime.expected_randomizedDigest_source_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_randomizedDigest_source_weight

/-- info: 'LeanSphincs.Lifetime.expected_randomizedDigest_source_weight_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_randomizedDigest_source_weight_bits

/-- info: 'LeanSphincs.Lifetime.newSourceRecordWeight_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.newSourceRecordWeight_same

/-- info: 'LeanSphincs.Lifetime.newSourceRecordWeight_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.newSourceRecordWeight_cons

/-- info: 'LeanSphincs.Lifetime.expected_signWithSources_source_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_signWithSources_source_weight

/-- info: 'LeanSphincs.Lifetime.expectedHashCost_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expectedHashCost_bind

/-- info: 'LeanSphincs.Lifetime.expectedHashCost_lift_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expectedHashCost_lift_prob

/-- info: 'LeanSphincs.Lifetime.expectedHashCost_private_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expectedHashCost_private_bind

/-- info: 'LeanSphincs.Lifetime.expectedHashCost_randomizedDigest_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expectedHashCost_randomizedDigest_succ

/-- info: 'LeanSphincs.Lifetime.expected_randomizedDigest_weight_le_hashCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_randomizedDigest_weight_le_hashCost

/-- info: 'LeanSphincs.Lifetime.expected_signWithSources_weight_le_grinding_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_signWithSources_weight_le_grinding_cost

/-- info: 'LeanSphincs.Lifetime.expected_signWithSources_weight_le_sign_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_signWithSources_weight_le_sign_cost

/-- info: 'LeanSphincs.Security.MaterialGameCoupling.programCache_eq_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.MaterialGameCoupling.programCache_eq_self

/-- info: 'LeanSphincs.Security.MaterialGameCoupling.prepared_query_support_cache_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.MaterialGameCoupling.prepared_query_support_cache_le

/-- info: 'LeanSphincs.Security.MaterialGameCoupling.prepared_support_cache_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.MaterialGameCoupling.prepared_support_cache_le

/-- info: 'LeanSphincs.Security.MaterialGameCoupling.sourceRun_eq_counted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.MaterialGameCoupling.sourceRun_eq_counted

/-- info: 'LeanSphincs.Security.MaterialGameCoupling.targetRun_eq_counted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.MaterialGameCoupling.targetRun_eq_counted

/-- info: 'LeanSphincs.Security.MaterialGameCoupling.Related.honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.MaterialGameCoupling.Related.honest

/-- info: 'LeanSphincs.Security.MaterialGameCoupling.sourceRun_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.MaterialGameCoupling.sourceRun_bind

/-- info: 'LeanSphincs.Security.MaterialGameCoupling.targetRun_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.MaterialGameCoupling.targetRun_bind

/-- info: 'LeanSphincs.Security.MaterialGameCoupling.Related.pure'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.MaterialGameCoupling.Related.pure'

/-- info: 'LeanSphincs.Security.MaterialGameCoupling.Related.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.MaterialGameCoupling.Related.bind

/-- info: 'LeanSphincs.Security.MaterialGameCoupling.Related.map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.MaterialGameCoupling.Related.map

/-- info: 'LeanSphincs.Security.MaterialGameCoupling.counted_ordinaryWorld_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.MaterialGameCoupling.counted_ordinaryWorld_query

/-- info: 'LeanSphincs.Security.MaterialGameCoupling.Related.ordinary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.MaterialGameCoupling.Related.ordinary

/-- info: 'LeanSphincs.Security.MaterialGameCoupling.Related.simulateQ_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.MaterialGameCoupling.Related.simulateQ_writer

/-- info: 'LeanSphincs.Security.MaterialGameCoupling.ordinaryWorld_lift_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.MaterialGameCoupling.ordinaryWorld_lift_hash

/-- info: 'LeanSphincs.Security.MaterialGameCoupling.Related.sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.MaterialGameCoupling.Related.sign

/-- info: 'LeanSphincs.Security.MaterialGameCoupling.Related.adversary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.MaterialGameCoupling.Related.adversary

/-- info: 'LeanSphincs.Security.MaterialGameCoupling.targetRun_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.MaterialGameCoupling.targetRun_map

/-- info: 'LeanSphincs.Security.MaterialGameCoupling.Related.bind_on_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.MaterialGameCoupling.Related.bind_on_support

/-- info: 'LeanSphincs.Security.MaterialGameCoupling.Related.rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.MaterialGameCoupling.Related.rest

/-- info: 'LeanSphincs.Security.MaterialGameCoupling.keygen_map_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.MaterialGameCoupling.keygen_map_root

/-- info: 'LeanSphincs.Security.MaterialGameCoupling.gameAfterSeed_eq_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.MaterialGameCoupling.gameAfterSeed_eq_bind

/-- info: 'LeanSphincs.Security.MaterialGameCoupling.materialGame_eq_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.MaterialGameCoupling.materialGame_eq_bind

/-- info: 'LeanSphincs.Security.MaterialGameCoupling.Related.gameAfterSeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.MaterialGameCoupling.Related.gameAfterSeed

/-- info: 'LeanSphincs.Security.MaterialGameCoupling.evalDist_gameAfterSeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.MaterialGameCoupling.evalDist_gameAfterSeed

/-- info: 'LeanSphincs.Security.MaterialGameCoupling.evalDist_experiment_material' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.MaterialGameCoupling.evalDist_experiment_material

/-- info: 'LeanSphincs.Security.Graph.positionAt_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.positionAt_some_iff

/-- info: 'LeanSphincs.Security.Graph.referenceTable_active' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.referenceTable_active

/-- info: 'LeanSphincs.Security.Graph.referenceTable_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.referenceTable_boundary

/-- info: 'LeanSphincs.Security.Graph.canonical_target_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.canonical_target_empty

/-- info: 'LeanSphincs.Security.Graph.target_has_position' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.target_has_position

/-- info: 'LeanSphincs.Security.Graph.freshStructural_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.freshStructural_clean

/-- info: 'LeanSphincs.Security.Graph.query_cache_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.query_cache_origin

/-- info: 'LeanSphincs.Security.Graph.hash_cache_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.hash_cache_origin

/-- info: 'LeanSphincs.Security.Graph.prepare_cache_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.prepare_cache_clean

/-- info: 'LeanSphincs.Security.Graph.material_freshStructural' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.material_freshStructural

/-- info: 'LeanSphincs.Security.Graph.prepare_labels_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.prepare_labels_consistent

/-- info: 'LeanSphincs.Security.Graph.prepare_labels_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.prepare_labels_boundary

/-- info: 'LeanSphincs.Security.Graph.prepared_structural_target_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.prepared_structural_target_bound

/-- info: 'LeanSphincs.Security.quotient_eq_sibling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.quotient_eq_sibling

/-- info: 'LeanSphincs.Security.xor_one_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.xor_one_ne

/-- info: 'LeanSphincs.Security.boundary_not_kept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.boundary_not_kept

/-- info: 'LeanSphincs.Security.outside_subtree_addressed_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.outside_subtree_addressed_witness

/-- info: 'LeanSphincs.Security.PrunedGraph.boundary_inactive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PrunedGraph.boundary_inactive

/-- info: 'LeanSphincs.Security.PrunedGraph.spineIndex_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PrunedGraph.spineIndex_lt

/-- info: 'LeanSphincs.Security.PrunedGraph.boundaryIndex_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PrunedGraph.boundaryIndex_lt

/-- info: 'LeanSphincs.Security.PrunedGraph.boundaryPosition_domain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PrunedGraph.boundaryPosition_domain

/-- info: 'LeanSphincs.Security.PrunedGraph.boundaryPosition_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PrunedGraph.boundaryPosition_value

/-- info: 'LeanSphincs.Security.PrunedGraph.initialLabels_boundary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PrunedGraph.initialLabels_boundary

/-- info: 'LeanSphincs.Security.PrunedGraph.prepared_boundary_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PrunedGraph.prepared_boundary_value

/-- info: 'LeanSphincs.Security.PrunedGraph.referenceTable_surrogate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PrunedGraph.referenceTable_surrogate

/-- info: 'LeanSphincs.Security.PrunedGraph.cached_surrogate_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.PrunedGraph.cached_surrogate_bad

/-- info: 'LeanSphincs.Lifetime.cachedRecordContribution_eq_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.cachedRecordContribution_eq_charge

/-- info: 'LeanSphincs.Lifetime.newCachedDisclosureWeight_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.newCachedDisclosureWeight_same

/-- info: 'LeanSphincs.Lifetime.newCachedDisclosureWeight_eq_source_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.newCachedDisclosureWeight_eq_source_weight

/-- info: 'LeanSphincs.Lifetime.expected_newCachedDisclosureWeight_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_newCachedDisclosureWeight_le

/-- info: 'LeanSphincs.Lifetime.digestForecast_rejected_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.digestForecast_rejected_eq_zero

/-- info: 'LeanSphincs.Lifetime.RejectedGrindingPrefix.refl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.RejectedGrindingPrefix.refl

/-- info: 'LeanSphincs.Lifetime.RejectedGrindingPrefix.query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.RejectedGrindingPrefix.query

/-- info: 'LeanSphincs.Lifetime.RejectedGrindingPrefix.forecast_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.RejectedGrindingPrefix.forecast_le

/-- info: 'LeanSphincs.Lifetime.expected_selectedDigestForecast_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_selectedDigestForecast_le

/-- info: 'LeanSphincs.Lifetime.newSourceDigestWeight_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.newSourceDigestWeight_same

/-- info: 'LeanSphincs.Lifetime.expected_signWithSources_digest_weight_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_signWithSources_digest_weight_le

/-- info: 'LeanSphincs.Lifetime.expected_prequeried_source_contribution_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_prequeried_source_contribution_le

/-- info: 'LeanSphincs.Lifetime.digestForecast_congr_cache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.digestForecast_congr_cache

/-- info: 'LeanSphincs.Lifetime.digestForecast_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.digestForecast_mono

/-- info: 'LeanSphincs.Lifetime.pairForecast_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pairForecast_comm

/-- info: 'LeanSphincs.Lifetime.digestForecast_query_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.digestForecast_query_other

/-- info: 'LeanSphincs.Lifetime.expected_pairForecast_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_pairForecast_query

/-- info: 'LeanSphincs.Lifetime.pairForecast_fresh_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pairForecast_fresh_source

/-- info: 'LeanSphincs.Lifetime.pairForecast_fresh_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pairForecast_fresh_target

/-- info: 'LeanSphincs.Lifetime.mem_messageRandomizers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.mem_messageRandomizers

/-- info: 'LeanSphincs.Lifetime.randomizer_forecast_sum_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.randomizer_forecast_sum_split

/-- info: 'LeanSphincs.Lifetime.randomizerAverage_forecast_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.randomizerAverage_forecast_split

/-- info: 'LeanSphincs.Lifetime.randomizerAverage_forecast_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.randomizerAverage_forecast_balance

/-- info: 'LeanSphincs.Security.Prefix.hashCalls_pure' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.hashCalls_pure

/-- info: 'LeanSphincs.Security.Prefix.hashCalls_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.hashCalls_bind

/-- info: 'LeanSphincs.Security.Prefix.hashCalls_oracleHash' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.hashCalls_oracleHash

/-- info: 'LeanSphincs.Security.Prefix.hashCalls_tweakableHash' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.hashCalls_tweakableHash

/-- info: 'LeanSphincs.Security.Prefix.hashCalls_deriveKey' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.hashCalls_deriveKey

/-- info: 'LeanSphincs.Security.Prefix.hashCalls_sequenceFin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.hashCalls_sequenceFin

/-- info: 'LeanSphincs.Security.Prefix.hashCalls_chainWalk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.hashCalls_chainWalk

/-- info: 'LeanSphincs.Security.Prefix.hashCalls_oneTimePublicKey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.hashCalls_oneTimePublicKey

/-- info: 'LeanSphincs.Security.Prefix.hashCalls_treeNode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.hashCalls_treeNode

/-- info: 'LeanSphincs.Security.Prefix.hashCalls_ftsNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.hashCalls_ftsNode

/-- info: 'LeanSphincs.Security.Prefix.hashCalls_ftsKey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.hashCalls_ftsKey

/-- info: 'LeanSphincs.Security.Prefix.hashCalls_ftsOpen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.hashCalls_ftsOpen

/-- info: 'LeanSphincs.Security.Prefix.hashCalls_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.hashCalls_encode

/-- info: 'LeanSphincs.Security.Prefix.hashCalls_otsSignFrom_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.hashCalls_otsSignFrom_answer

/-- info: 'LeanSphincs.Security.Prefix.hashCalls_surrogate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.hashCalls_surrogate

/-- info: 'LeanSphincs.Security.Prefix.hashCalls_treePath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.hashCalls_treePath

/-- info: 'LeanSphincs.Security.Prefix.hashCalls_signLayer_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.hashCalls_signLayer_answer

/-- info: 'LeanSphincs.Security.Prefix.hashCalls_sequenceLayers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.hashCalls_sequenceLayers

/-- info: 'LeanSphincs.Security.Prefix.hashCalls_messageDigestCall' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.hashCalls_messageDigestCall

/-- info: 'LeanSphincs.Security.Prefix.hashCalls_messageDigest' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.hashCalls_messageDigest

/-- info: 'LeanSphincs.Security.Prefix.hashCalls_signAttempt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.hashCalls_signAttempt

/-- info: 'LeanSphincs.Security.Prefix.hashCalls_finishSign_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.hashCalls_finishSign_answer

/-- info: 'LeanSphincs.Security.Prefix.counted_lift_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.counted_lift_hash

/-- info: 'LeanSphincs.Security.Prefix.counted_lift_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.counted_lift_prob

/-- info: 'LeanSphincs.Security.Prefix.eval_counted_hash' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.eval_counted_hash

/-- info: 'LeanSphincs.Security.Prefix.fixedHashWorld_counted_lift_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.fixedHashWorld_counted_lift_hash

/-- info: 'LeanSphincs.Security.Prefix.counted_signDigestLoop_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.counted_signDigestLoop_answer

/-- info: 'LeanSphincs.Security.Prefix.publicSignWithCost_replaceSecret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.publicSignWithCost_replaceSecret

/-- info: 'LeanSphincs.Security.Prefix.counted_sign_from_referenceCutoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.counted_sign_from_referenceCutoff

/-- info: 'LeanSphincs.Security.Prefix.address_segmentAt' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.address_segmentAt

/-- info: 'LeanSphincs.Security.Prefix.selectedPrefix_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.selectedPrefix_hash

/-- info: 'LeanSphincs.Security.Prefix.selectedPrefix_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.selectedPrefix_unique

/-- info: 'LeanSphincs.Security.Prefix.selectedPrefix_sum_le_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.selectedPrefix_sum_le_hash

/-- info: 'LeanSphincs.Security.Prefix.prefix_calls_sum_le_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.prefix_calls_sum_le_hash

/-- info: 'LeanSphincs.Security.Prefix.recorded_prefix_calls_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.recorded_prefix_calls_sum_le

/-- info: 'LeanSphincs.Security.Prefix.countedPrefix_splitWorld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.countedPrefix_splitWorld

/-- info: 'LeanSphincs.Security.Prefix.realRun_counted_byte_distribution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.realRun_counted_byte_distribution

/-- info: 'LeanSphincs.Security.Prefix.splitWorld_ideal_spent_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.splitWorld_ideal_spent_lower

/-- info: 'LeanSphincs.Security.Prefix.splitWorld_twoEdge_bound_real_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.splitWorld_twoEdge_bound_real_cost

/-- info: 'LeanSphincs.Security.Prefix.eval_compileHash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.eval_compileHash

/-- info: 'LeanSphincs.Security.Prefix.fixedPreparedWorld_lift_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.fixedPreparedWorld_lift_hash

/-- info: 'LeanSphincs.Security.Prefix.fixedPreparedWorld_compileWorld_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.fixedPreparedWorld_compileWorld_query

/-- info: 'LeanSphincs.Security.Prefix.fixedPreparedWorld_compileWorld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.fixedPreparedWorld_compileWorld

/-- info: 'LeanSphincs.Security.Prefix.preparedOracle_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.preparedOracle_answer

/-- info: 'LeanSphincs.Security.Prefix.derivedSecrets_prepared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.derivedSecrets_prepared

/-- info: 'LeanSphincs.Security.Prefix.counted_prepared_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.counted_prepared_sign

/-- info: 'LeanSphincs.Security.Prefix.counted_prepared_sign_from_referenceCutoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.counted_prepared_sign_from_referenceCutoff

/-- info: 'LeanSphincs.Security.Prefix.replaceMaterial_parameter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.replaceMaterial_parameter

/-- info: 'LeanSphincs.Security.Prefix.replaceMaterial_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.replaceMaterial_self

/-- info: 'LeanSphincs.Security.Prefix.replaceMaterial_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.replaceMaterial_other

/-- info: 'LeanSphincs.Security.Prefix.replaceMaterial_twice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.replaceMaterial_twice

/-- info: 'LeanSphincs.Security.Prefix.replaceMaterial_current' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.replaceMaterial_current

/-- info: 'LeanSphincs.Security.Prefix.materialSecrets_replaceMaterial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.materialSecrets_replaceMaterial

/-- info: 'LeanSphincs.Security.Prefix.uniform_material' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.uniform_material

/-- info: 'LeanSphincs.Security.SeedLoss.countPreparedQueries_query_bind' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.countPreparedQueries_query_bind

/-- info: 'LeanSphincs.Security.SeedLoss.countPreparedQueries_pure' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.countPreparedQueries_pure

/-- info: 'LeanSphincs.Security.SeedLoss.stopBefore_pure' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.stopBefore_pure

/-- info: 'LeanSphincs.Security.SeedLoss.stopBefore_query_bind' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.stopBefore_query_bind

/-- info: 'LeanSphincs.Security.SeedLoss.run'_query_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.run'_query_bind

/-- info: 'LeanSphincs.Security.SeedLoss.probEvent_stopBefore_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.probEvent_stopBefore_le

/-- info: 'LeanSphincs.Security.SeedLoss.probEvent_le_stopBefore_add_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.probEvent_le_stopBefore_add_failure

/-- info: 'LeanSphincs.Security.SeedLoss.traceHashes_pure' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.traceHashes_pure

/-- info: 'LeanSphincs.Security.SeedLoss.traceHashes_query_bind' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.traceHashes_query_bind

/-- info: 'LeanSphincs.Security.SeedLoss.traceHashes_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.traceHashes_length

/-- info: 'LeanSphincs.Security.SeedLoss.traceHashes_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.traceHashes_length_le

/-- info: 'LeanSphincs.Security.SeedLoss.traceHits_prepend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.traceHits_prepend

/-- info: 'LeanSphincs.Security.SeedLoss.probOutput_stopBefore_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.probOutput_stopBefore_none

/-- info: 'LeanSphincs.Security.SeedLoss.entryHit_probability_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.entryHit_probability_le

/-- info: 'LeanSphincs.Security.SeedLoss.traceHits_probability_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.traceHits_probability_le

/-- info: 'LeanSphincs.Security.SeedLoss.probOutput_stopBefore_seed_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.probOutput_stopBefore_seed_le

/-- info: 'LeanSphincs.Security.SeedLoss.queryBound_of_isQueryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.queryBound_of_isQueryBound

/-- info: 'LeanSphincs.Security.SeedLoss.cap_queryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.cap_queryBound

/-- info: 'LeanSphincs.Security.SeedLoss.capped_seed_hit_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.capped_seed_hit_bound

/-- info: 'LeanSphincs.Security.SeedLoss.agreeOutside_cacheQuery' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.agreeOutside_cacheQuery

/-- info: 'LeanSphincs.Security.SeedLoss.run'_stopBefore_seed_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.run'_stopBefore_seed_eq

/-- info: 'LeanSphincs.Security.SeedLoss.probEvent_cache_change_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.probEvent_cache_change_le

/-- info: 'LeanSphincs.Security.SeedLoss.probEvent_random_cache_change_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.probEvent_random_cache_change_le

/-- info: 'LeanSphincs.Security.SeedLoss.evalDist_run_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.evalDist_run_cap

/-- info: 'LeanSphincs.Security.SeedLoss.capWin_finish' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.capWin_finish

/-- info: 'LeanSphincs.Security.SeedLoss.probEvent_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.probEvent_cap

/-- info: 'LeanSphincs.Security.SeedLoss.entryCharge_virtual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.entryCharge_virtual

/-- info: 'LeanSphincs.Security.SeedLoss.entryCharge_verifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.entryCharge_verifier

/-- info: 'LeanSphincs.Security.SeedLoss.entryCharge_keygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.entryCharge_keygen

/-- info: 'LeanSphincs.Security.SeedLoss.entryCharge_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.entryCharge_le_one

/-- info: 'LeanSphincs.Security.SeedLoss.entryHit_probability_le_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.entryHit_probability_le_charge

/-- info: 'LeanSphincs.Security.SeedLoss.traceCharge_le_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.traceCharge_le_length

/-- info: 'LeanSphincs.Security.SeedLoss.traceHits_probability_le_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.traceHits_probability_le_charge

/-- info: 'LeanSphincs.Security.SeedLoss.probOutput_stopBefore_seed_le_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.probOutput_stopBefore_seed_le_charge

/-- info: 'LeanSphincs.Security.SeedLoss.expectedDerivationQueries_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.expectedDerivationQueries_le

/-- info: 'LeanSphincs.Security.SeedLoss.probEvent_random_cache_change_le_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.probEvent_random_cache_change_le_charge

/-- info: 'LeanSphincs.Security.SeedLoss.expected_partition_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.expected_partition_le

/-- info: 'LeanSphincs.Security.SeedLoss.forgeAdvantage_eq_programmed_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.forgeAdvantage_eq_programmed_cap

/-- info: 'LeanSphincs.Security.SeedLoss.forgeAdvantage_le_cappedMaterial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.forgeAdvantage_le_cappedMaterial

/-- info: 'LeanSphincs.Security.SeedLoss.materialDerivationQueries_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.materialDerivationQueries_le

/-- info: 'LeanSphincs.Security.SeedLoss.forgeAdvantage_le_cappedMaterial_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.forgeAdvantage_le_cappedMaterial_charge

/-- info: 'LeanSphincs.Security.SeedLoss.material_partition_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.material_partition_le

/-- info: 'LeanSphincs.Security.SeedLoss.forgeAdvantage_le_of_material_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedLoss.forgeAdvantage_le_of_material_charge

/-- info: 'LeanSphincs.Lifetime.pivotalPositions_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pivotalPositions_card_le

/-- info: 'LeanSphincs.Lifetime.pivotalPositions_card_eq_zero_of_not_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pivotalPositions_card_eq_zero_of_not_covered

/-- info: 'LeanSphincs.Lifetime.functionCovered_reindex_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.functionCovered_reindex_iff

/-- info: 'LeanSphincs.Lifetime.pivotalPosition_reindex_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pivotalPosition_reindex_iff

/-- info: 'LeanSphincs.Lifetime.probEvent_pivotal_position_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_pivotal_position_eq

/-- info: 'LeanSphincs.Lifetime.probEvent_pivotal_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_pivotal_mul_le

/-- info: 'LeanSphincs.Lifetime.pivotalPosition_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pivotalPosition_zero_iff

/-- info: 'LeanSphincs.Lifetime.probEvent_independent_marginal_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_independent_marginal_mul_le

/-- info: 'LeanSphincs.Lifetime.initial_independentMarginalWeight_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.initial_independentMarginalWeight_mul_le

/-- info: 'LeanSphincs.Lifetime.pairForecast_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pairForecast_product

/-- info: 'LeanSphincs.Lifetime.targetSecondForecast_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.targetSecondForecast_comm

/-- info: 'LeanSphincs.Lifetime.expected_targetSecondForecast_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_targetSecondForecast_query

/-- info: 'LeanSphincs.Lifetime.expected_secondBankValue_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_secondBankValue_query

/-- info: 'LeanSphincs.Lifetime.secondBankValue_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.secondBankValue_insert

/-- info: 'LeanSphincs.Lifetime.expected_secondBankStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_secondBankStep

/-- info: 'LeanSphincs.Lifetime.uniformDigestForecast_square_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.uniformDigestForecast_square_le

/-- info: 'LeanSphincs.Lifetime.expected_secondBankStep_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_secondBankStep_le

/-- info: 'LeanSphincs.Lifetime.expected_secondBankEnvelope_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_secondBankEnvelope_step

/-- info: 'LeanSphincs.Lifetime.expected_adaptiveSecondBank_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_adaptiveSecondBank_le

/-- info: 'LeanSphincs.Lifetime.expected_adaptiveSecondBank_empty_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_adaptiveSecondBank_empty_le

/-- info: 'LeanSphincs.Lifetime.digestForecast_cachedSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.digestForecast_cachedSource

/-- info: 'LeanSphincs.Lifetime.secondBankValue_resolved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.secondBankValue_resolved

/-- info: 'LeanSphincs.Lifetime.secondBankValue_congr_cache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.secondBankValue_congr_cache

/-- info: 'LeanSphincs.Lifetime.expected_jointSecondBankValue_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_jointSecondBankValue_query

/-- info: 'LeanSphincs.Lifetime.expected_jointSecondBankStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_jointSecondBankStep

/-- info: 'LeanSphincs.Lifetime.requested_scaled_lifetime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.requested_scaled_lifetime

/-- info: 'LeanSphincs.Lifetime.requested_pair_fors_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.requested_pair_fors_bound

/-- info: 'LeanSphincs.Lifetime.requested_localizedVarianceRate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.requested_localizedVarianceRate

/-- info: 'LeanSphincs.Lifetime.localized_variance_exception_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.localized_variance_exception_budget

/-- info: 'LeanSphincs.Lifetime.uniformDisclosureSet_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.uniformDisclosureSet_insert

/-- info: 'LeanSphincs.Lifetime.probEvent_coverage_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_coverage_insert

/-- info: 'LeanSphincs.Lifetime.futureCoverWeight_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.futureCoverWeight_insert

/-- info: 'LeanSphincs.Lifetime.futureCoverWeight_succ_gain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.futureCoverWeight_succ_gain

/-- info: 'LeanSphincs.Lifetime.signWithSources_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.signWithSources_mass

/-- info: 'LeanSphincs.Lifetime.signWithSources_future_gain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.signWithSources_future_gain

/-- info: 'LeanSphincs.Lifetime.expected_signWithSources_centered_gain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_signWithSources_centered_gain

/-- info: 'LeanSphincs.Lifetime.poolCount_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.poolCount_eq_sum

/-- info: 'LeanSphincs.Lifetime.poolHit_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.poolHit_independent

/-- info: 'LeanSphincs.Lifetime.poolHit_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.poolHit_mean

/-- info: 'LeanSphincs.Lifetime.poolHit_subGaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.poolHit_subGaussian

/-- info: 'LeanSphincs.Lifetime.indexPool_upper_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.indexPool_upper_tail

/-- info: 'LeanSphincs.Lifetime.indexPool_lower_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.indexPool_lower_tail

/-- info: 'LeanSphincs.Lifetime.indexPool_bad_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.indexPool_bad_index

/-- info: 'LeanSphincs.Lifetime.indexPool_unbalanced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.indexPool_unbalanced

/-- info: 'LeanSphincs.Lifetime.indexPoolMeasure_eq_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.indexPoolMeasure_eq_uniform

/-- info: 'LeanSphincs.Lifetime.poolFamily_unbalanced_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.poolFamily_unbalanced_key

/-- info: 'LeanSphincs.Lifetime.poolFamily_unbalanced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.poolFamily_unbalanced

/-- info: 'LeanSphincs.Lifetime.pool_concentration_exp_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pool_concentration_exp_bound

/-- info: 'LeanSphincs.Lifetime.poolFamily_unbalanced_negligible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.poolFamily_unbalanced_negligible

/-- info: 'LeanSphincs.Lifetime.indexPoolFamilyMeasure_eq_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.indexPoolFamilyMeasure_eq_uniform

/-- info: 'LeanSphincs.Lifetime.PoolBalanced.count_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.PoolBalanced.count_lower

/-- info: 'LeanSphincs.Lifetime.PoolBalanced.count_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.PoolBalanced.count_upper

/-- info: 'LeanSphincs.Lifetime.PoolBalanced.accepted_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.PoolBalanced.accepted_lower

/-- info: 'LeanSphincs.Lifetime.PoolBalanced.accepted_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.PoolBalanced.accepted_positive

/-- info: 'LeanSphincs.Lifetime.PoolBalanced.accepted_index_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.PoolBalanced.accepted_index_ratio

/-- info: 'LeanSphincs.Lifetime.poolAcceptedCount_eq_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.poolAcceptedCount_eq_card

/-- info: 'LeanSphincs.Lifetime.pool_uniform_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pool_uniform_index

/-- info: 'LeanSphincs.Lifetime.pool_uniform_landing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pool_uniform_landing

/-- info: 'LeanSphincs.Lifetime.poolGrind_index_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.poolGrind_index_factor

/-- info: 'LeanSphincs.Lifetime.poolGrind_index_le_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.poolGrind_index_le_ratio

/-- info: 'LeanSphincs.Lifetime.balanced_poolGrind_index_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.balanced_poolGrind_index_bound

/-- info: 'LeanSphincs.Lifetime.poolGrindRandomness_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.poolGrindRandomness_factor

/-- info: 'LeanSphincs.Lifetime.poolGrindRandomness_weighted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.poolGrindRandomness_weighted

/-- info: 'LeanSphincs.Security.GraphCorrectness.one_lt_leaf_capacity' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.one_lt_leaf_capacity

/-- info: 'LeanSphincs.Security.GraphCorrectness.chain_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.chain_value

/-- info: 'LeanSphincs.Security.GraphCorrectness.leaf_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.leaf_input

/-- info: 'LeanSphincs.Security.GraphCorrectness.leaf_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.leaf_value

/-- info: 'LeanSphincs.Security.GraphCorrectness.tree_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.tree_input

/-- info: 'LeanSphincs.Security.GraphCorrectness.fors_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.fors_input

/-- info: 'LeanSphincs.Security.GraphCorrectness.child_index_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.child_index_bound

/-- info: 'LeanSphincs.Security.GraphCorrectness.fors_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.fors_value

/-- info: 'LeanSphincs.Security.GraphCorrectness.fors_roots_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.fors_roots_input

/-- info: 'LeanSphincs.Security.GraphCorrectness.fors_key_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.fors_key_value

/-- info: 'LeanSphincs.Security.GraphCorrectness.double_div_pow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.double_div_pow

/-- info: 'LeanSphincs.Security.GraphCorrectness.treePosition_active_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.treePosition_active_below

/-- info: 'LeanSphincs.Security.GraphCorrectness.tree_value_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.tree_value_below

/-- info: 'LeanSphincs.Security.GraphCorrectness.spineIndex_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.spineIndex_range

/-- info: 'LeanSphincs.Security.GraphCorrectness.spineIndex_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.spineIndex_step

/-- info: 'LeanSphincs.Security.GraphCorrectness.spinePosition_active' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.spinePosition_active

/-- info: 'LeanSphincs.Security.GraphCorrectness.boundary_tree_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.boundary_tree_value

/-- info: 'LeanSphincs.Security.GraphCorrectness.tree_input_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.tree_input_ordered

/-- info: 'LeanSphincs.Security.GraphCorrectness.spine_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.spine_value

/-- info: 'LeanSphincs.Security.GraphCorrectness.chain_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.chain_input

/-- info: 'LeanSphincs.Security.GraphCorrectness.quotient_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.quotient_range

/-- info: 'LeanSphincs.Security.GraphCorrectness.pathNode_kept' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.pathNode_kept

/-- info: 'LeanSphincs.Security.GraphCorrectness.pathSibling_kept' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.pathSibling_kept

/-- info: 'LeanSphincs.Security.GraphCorrectness.canonicalPath_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.canonicalPath_below

/-- info: 'LeanSphincs.Security.GraphCorrectness.tree_path_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.tree_path_value

/-- info: 'LeanSphincs.Security.GraphCorrectness.tree_path_sibling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.tree_path_sibling

/-- info: 'LeanSphincs.Security.GraphCorrectness.tree_path_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.tree_path_input

/-- info: 'LeanSphincs.Security.GraphCorrectness.tree_path_active' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.tree_path_active

/-- info: 'LeanSphincs.Security.GraphCorrectness.tree_root_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.tree_root_value

/-- info: 'LeanSphincs.Security.GraphCorrectness.fors_leaf_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.fors_leaf_input

/-- info: 'LeanSphincs.Security.GraphCorrectness.fors_input_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.fors_input_ordered

/-- info: 'LeanSphincs.Security.GraphCorrectness.fors_path_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.fors_path_value

/-- info: 'LeanSphincs.Security.GraphCorrectness.fors_path_sibling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.fors_path_sibling

/-- info: 'LeanSphincs.Security.GraphCorrectness.fors_path_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.fors_path_input

/-- info: 'LeanSphincs.Security.GraphCorrectness.materialOts_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.materialOts_eq

/-- info: 'LeanSphincs.Security.GraphCorrectness.materialFts_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.materialFts_eq

/-- info: 'LeanSphincs.Security.GraphCorrectness.materialSurrogates_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.materialSurrogates_eq

/-- info: 'LeanSphincs.Security.GraphCorrectness.prepared_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.prepared_consistent

/-- info: 'LeanSphincs.Security.GraphCorrectness.prepared_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.prepared_boundary

/-- info: 'LeanSphincs.Security.GraphCorrectness.prepared_root_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.prepared_root_value

/-- info: 'LeanSphincs.Security.GraphCorrectness.prepared_fors_key_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphCorrectness.prepared_fors_key_value

/-- info: 'LeanSphincs.Security.Prefix.PublicAgreement.tweakable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.PublicAgreement.tweakable

/-- info: 'LeanSphincs.Security.Prefix.PublicAgreement.chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.PublicAgreement.chain

/-- info: 'LeanSphincs.Security.Prefix.PublicAgreement.encoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.PublicAgreement.encoding

/-- info: 'LeanSphincs.Security.Prefix.PublicAgreement.firstEncoding_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.PublicAgreement.firstEncoding_eq

/-- info: 'LeanSphincs.Security.Prefix.PublicAgreement.forsNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.PublicAgreement.forsNode

/-- info: 'LeanSphincs.Security.Prefix.PublicAgreement.forsKey' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.PublicAgreement.forsKey

/-- info: 'LeanSphincs.Security.Prefix.PublicAgreement.forsOpen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.PublicAgreement.forsOpen

/-- info: 'LeanSphincs.Security.Prefix.PublicAgreement.digestCall' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.PublicAgreement.digestCall

/-- info: 'LeanSphincs.Security.Prefix.PublicAgreement.digest' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.PublicAgreement.digest

/-- info: 'LeanSphincs.Security.Prefix.PublicAgreement.endpoints' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.PublicAgreement.endpoints

/-- info: 'LeanSphincs.Security.Prefix.PublicAgreement.node' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.PublicAgreement.node

/-- info: 'LeanSphincs.Security.Prefix.PublicAgreement.values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.PublicAgreement.values

/-- info: 'LeanSphincs.Security.Prefix.PublicAgreement.spine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.PublicAgreement.spine

/-- info: 'LeanSphincs.Security.Prefix.PublicAgreement.path' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.PublicAgreement.path

/-- info: 'LeanSphincs.Security.Prefix.PublicAgreement.layer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.PublicAgreement.layer

/-- info: 'LeanSphincs.Security.Prefix.PublicAgreement.finishSign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.PublicAgreement.finishSign

/-- info: 'LeanSphincs.Security.Prefix.PublicAgreement.cutoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.PublicAgreement.cutoff

/-- info: 'LeanSphincs.Security.Prefix.prepared_replaceMaterial_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.prepared_replaceMaterial_agreement

/-- info: 'LeanSphincs.Security.Prefix.publicFinishSign_replaceMaterial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.publicFinishSign_replaceMaterial

/-- info: 'LeanSphincs.Security.Prefix.PublicAgreement.otsCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.PublicAgreement.otsCost

/-- info: 'LeanSphincs.Security.Prefix.PublicAgreement.layerCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.PublicAgreement.layerCost

/-- info: 'LeanSphincs.Security.Prefix.PublicAgreement.finishCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.PublicAgreement.finishCost

/-- info: 'LeanSphincs.Security.Prefix.PublicAgreement.signAttempt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.PublicAgreement.signAttempt

/-- info: 'LeanSphincs.Security.Prefix.PublicAgreement.countedDigest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.PublicAgreement.countedDigest

/-- info: 'LeanSphincs.Security.Prefix.PublicAgreement.signWithCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.PublicAgreement.signWithCost

/-- info: 'LeanSphincs.Security.Prefix.publicSignWithCost_replaceMaterial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.publicSignWithCost_replaceMaterial

/-- info: 'LeanSphincs.Security.Prefix.surrogate_replaceMaterial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.surrogate_replaceMaterial

/-- info: 'LeanSphincs.Security.Prefix.erasedMaterialSign_replaceMaterial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.erasedMaterialSign_replaceMaterial

/-- info: 'LeanSphincs.Security.Prefix.counted_prepared_sign_erased' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.counted_prepared_sign_erased

/-- info: 'LeanSphincs.Security.Prefix.eval_compiledHash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.eval_compiledHash

/-- info: 'LeanSphincs.Security.Prefix.hashCalls_spineNode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.hashCalls_spineNode

/-- info: 'LeanSphincs.Security.Prefix.hashCalls_keygenFromSeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.hashCalls_keygenFromSeed

/-- info: 'LeanSphincs.Security.Prefix.publicSpine_replaceMaterial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.publicSpine_replaceMaterial

/-- info: 'LeanSphincs.Security.Prefix.erasedMaterialRoot_replaceMaterial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.erasedMaterialRoot_replaceMaterial

/-- info: 'LeanSphincs.Security.Prefix.prepared_root_erased' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.prepared_root_erased

/-- info: 'LeanSphincs.Security.Prefix.prepared_keygen_erased' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.prepared_keygen_erased

/-- info: 'LeanSphincs.Lifetime.fixed_signDigestLoop_eq_poolGrindRandomness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fixed_signDigestLoop_eq_poolGrindRandomness

/-- info: 'LeanSphincs.Lifetime.adaptiveHitCount_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.adaptiveHitCount_moment

/-- info: 'LeanSphincs.Lifetime.adaptiveHitCount_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.adaptiveHitCount_tail

/-- info: 'LeanSphincs.Lifetime.occupancy_exponential_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.occupancy_exponential_bound

/-- info: 'LeanSphincs.Lifetime.adaptiveHitCount_tail_256' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.adaptiveHitCount_tail_256

/-- info: 'LeanSphincs.Lifetime.global_occupancy_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.global_occupancy_tail

/-- info: 'LeanSphincs.Lifetime.firstPoolInput_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.firstPoolInput_injective

/-- info: 'LeanSphincs.Lifetime.firstPoolCache_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.firstPoolCache_apply

/-- info: 'LeanSphincs.Lifetime.evalDist_firstPool_preparation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.evalDist_firstPool_preparation

/-- info: 'LeanSphincs.Lifetime.evalDist_firstPool_continuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.evalDist_firstPool_continuation

/-- info: 'LeanSphincs.Lifetime.evalDist_uniform_table_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.evalDist_uniform_table_map

/-- info: 'LeanSphincs.Lifetime.evalDist_firstPoolIndexes_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.evalDist_firstPoolIndexes_uniform

/-- info: 'LeanSphincs.Lifetime.probEvent_firstPool_unbalanced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_firstPool_unbalanced

/-- info: 'LeanSphincs.Lifetime.run_signDigestLoop_firstPool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.run_signDigestLoop_firstPool

/-- info: 'LeanSphincs.Lifetime.indexHitStep_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.indexHitStep_probability

/-- info: 'LeanSphincs.Lifetime.adaptiveIndexTrace_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.adaptiveIndexTrace_count

/-- info: 'LeanSphincs.Lifetime.adaptiveIndexTrace_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.adaptiveIndexTrace_tail

/-- info: 'LeanSphincs.Lifetime.requested_pool_occupancy_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.requested_pool_occupancy_mean

/-- info: 'LeanSphincs.Lifetime.requested_adaptive_occupancy_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.requested_adaptive_occupancy_tail

/-- info: 'LeanSphincs.Lifetime.candidateInput_position_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.candidateInput_position_injective

/-- info: 'LeanSphincs.Lifetime.decodeCandidateInput_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.decodeCandidateInput_self

/-- info: 'LeanSphincs.Lifetime.decodeCandidateInput_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.decodeCandidateInput_some

/-- info: 'LeanSphincs.Lifetime.otherDigestCall_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.otherDigestCall_ne

/-- info: 'LeanSphincs.Lifetime.candidate_other_input_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.candidate_other_input_ne

/-- info: 'LeanSphincs.Lifetime.evalDist_pairedRom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.evalDist_pairedRom

/-- info: 'LeanSphincs.Lifetime.pairedHash_candidate_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pairedHash_candidate_run

/-- info: 'LeanSphincs.Lifetime.pairedHash_fresh_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pairedHash_fresh_run

/-- info: 'LeanSphincs.Lifetime.cachedPairDigest_two_updates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.cachedPairDigest_two_updates

/-- info: 'LeanSphincs.Lifetime.evalDist_pairedHash_fresh_digest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.evalDist_pairedHash_fresh_digest

/-- info: 'LeanSphincs.Lifetime.PairedCache.empty' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.PairedCache.empty

/-- info: 'LeanSphincs.Lifetime.PairedCache.fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.PairedCache.fresh

/-- info: 'LeanSphincs.Lifetime.decodeCandidateInput_none_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.decodeCandidateInput_none_ne

/-- info: 'LeanSphincs.Lifetime.pairedHash_support_cache_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pairedHash_support_cache_le

/-- info: 'LeanSphincs.Lifetime.pairedHash_support_paired' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pairedHash_support_paired

/-- info: 'LeanSphincs.Lifetime.pairedHit_candidate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pairedHit_candidate

/-- info: 'LeanSphincs.Lifetime.pairedHash_hit_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pairedHash_hit_probability

/-- info: 'LeanSphincs.Lifetime.pairedHash_hit_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pairedHash_hit_le

/-- info: 'LeanSphincs.Lifetime.pairedRom_support_paired' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pairedRom_support_paired

/-- info: 'LeanSphincs.Lifetime.pairedRun_support_paired' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pairedRun_support_paired

/-- info: 'LeanSphincs.Lifetime.viewCap_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.viewCap_insert

/-- info: 'LeanSphincs.Lifetime.coverageGain_index_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.coverageGain_index_eq

/-- info: 'LeanSphincs.Lifetime.futureCoverageGain_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.futureCoverageGain_split

/-- info: 'LeanSphincs.Lifetime.overflowCoverageGain_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.overflowCoverageGain_le

/-- info: 'LeanSphincs.Lifetime.localizedCoverageGain_le_gain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.localizedCoverageGain_le_gain

/-- info: 'LeanSphincs.Lifetime.localizedCoverageGain_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.localizedCoverageGain_le_one

/-- info: 'LeanSphincs.Lifetime.localizedCoverageGain_square_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.localizedCoverageGain_square_le

/-- info: 'LeanSphincs.Lifetime.viewCoordinates_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.viewCoordinates_card_le

/-- info: 'LeanSphincs.Lifetime.fixedKeptCovered_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fixedKeptCovered_card

/-- info: 'LeanSphincs.Lifetime.probEvent_fixedKeptCovered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_fixedKeptCovered

/-- info: 'LeanSphincs.Lifetime.probEvent_landed_fixedKeptCovered_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_landed_fixedKeptCovered_le

/-- info: 'LeanSphincs.Lifetime.coverageGain_fixedKeptCovered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.coverageGain_fixedKeptCovered

/-- info: 'LeanSphincs.Lifetime.probEvent_landed_coverageGain_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_landed_coverageGain_le

/-- info: 'LeanSphincs.Lifetime.uniform_localizedCoverageGain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.uniform_localizedCoverageGain

/-- info: 'LeanSphincs.Lifetime.uniform_localizedCoverageGain_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.uniform_localizedCoverageGain_le

/-- info: 'LeanSphincs.Lifetime.localizedGainMean_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.localizedGainMean_le

/-- info: 'LeanSphincs.Lifetime.expected_signWithSources_localized_drift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_signWithSources_localized_drift

/-- info: 'LeanSphincs.Security.HiddenReveal.completion_known' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenReveal.completion_known

/-- info: 'LeanSphincs.Security.HiddenReveal.completion_reveal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenReveal.completion_reveal

/-- info: 'LeanSphincs.Security.HiddenReveal.completion_guess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenReveal.completion_guess

/-- info: 'LeanSphincs.Security.HiddenReveal.run_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenReveal.run_pure

/-- info: 'LeanSphincs.Security.HiddenReveal.run_private' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenReveal.run_private

/-- info: 'LeanSphincs.Security.HiddenReveal.run_reveal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenReveal.run_reveal

/-- info: 'LeanSphincs.Security.HiddenReveal.run_guess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenReveal.run_guess

/-- info: 'LeanSphincs.Security.HiddenReveal.adaptive_guess_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenReveal.adaptive_guess_bound

/-- info: 'LeanSphincs.Security.HiddenReveal.charge_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenReveal.charge_pure

/-- info: 'LeanSphincs.Security.HiddenReveal.charge_private' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenReveal.charge_private

/-- info: 'LeanSphincs.Security.HiddenReveal.charge_reveal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenReveal.charge_reveal

/-- info: 'LeanSphincs.Security.HiddenReveal.charge_guess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenReveal.charge_guess

/-- info: 'LeanSphincs.Security.HiddenReveal.adaptive_guess_bound_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenReveal.adaptive_guess_bound_charge

/-- info: 'LeanSphincs.Security.HiddenReveal.comparison_charge_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenReveal.comparison_charge_le

/-- info: 'LeanSphincs.Security.HiddenReveal.expectedGuessCharge_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenReveal.expectedGuessCharge_le

/-- info: 'LeanSphincs.Security.ExponentialCharge.run_pure' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.ExponentialCharge.run_pure

/-- info: 'LeanSphincs.Security.ExponentialCharge.run_query_bind' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.ExponentialCharge.run_query_bind

/-- info: 'LeanSphincs.Security.ExponentialCharge.run_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.ExponentialCharge.run_erase

/-- info: 'LeanSphincs.Security.ExponentialCharge.expected_normalized_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.ExponentialCharge.expected_normalized_le

/-- info: 'LeanSphincs.Security.ExponentialCharge.moment_le_of_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.ExponentialCharge.moment_le_of_normalized

/-- info: 'LeanSphincs.Security.ExponentialCharge.tail_mul_le_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.ExponentialCharge.tail_mul_le_moment

/-- info: 'LeanSphincs.Security.ExponentialCharge.tail_le_of_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.ExponentialCharge.tail_le_of_normalized

/-- info: 'LeanSphincs.Security.Prefix.counted_fixedPreparedCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.counted_fixedPreparedCost

/-- info: 'LeanSphincs.Security.Prefix.fixedPreparedCost_ordinary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.fixedPreparedCost_ordinary

/-- info: 'LeanSphincs.Security.Prefix.map_logging_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.map_logging_query

/-- info: 'LeanSphincs.Security.Prefix.map_lift_query' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.map_lift_query

/-- info: 'LeanSphincs.Security.Prefix.fixedPreparedCost_ordinary_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.fixedPreparedCost_ordinary_program

/-- info: 'LeanSphincs.Security.Prefix.fixedPreparedCost_lift_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.fixedPreparedCost_lift_hash

/-- info: 'LeanSphincs.Security.Prefix.countHashQueries_eq_sourceCount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.countHashQueries_eq_sourceCount

/-- info: 'LeanSphincs.Security.Prefix.fixedPreparedCost_sign_erased' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.fixedPreparedCost_sign_erased

/-- info: 'LeanSphincs.Security.Prefix.erasedInteraction_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.erasedInteraction_eq

/-- info: 'LeanSphincs.Security.Prefix.counted_adversary_erased' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.counted_adversary_erased

/-- info: 'LeanSphincs.Security.Prefix.erasedInteraction_replaceMaterial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.erasedInteraction_replaceMaterial

/-- info: 'LeanSphincs.Security.Prefix.erased_adversary_replaceMaterial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.erased_adversary_replaceMaterial

/-- info: 'LeanSphincs.Security.Prefix.fixedPreparedCost_rest_erased' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.fixedPreparedCost_rest_erased

/-- info: 'LeanSphincs.Security.Prefix.erasedRest_replaceMaterial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.erasedRest_replaceMaterial

/-- info: 'LeanSphincs.Security.Prefix.fixedPreparedCost_keygen_erased' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.fixedPreparedCost_keygen_erased

/-- info: 'LeanSphincs.Security.Prefix.counted_materialGame_erased' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.counted_materialGame_erased

/-- info: 'LeanSphincs.Security.Prefix.erasedGame_replaceMaterial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.erasedGame_replaceMaterial

/-- info: 'LeanSphincs.Security.Graph.freshPositions_of_structural' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.freshPositions_of_structural

/-- info: 'LeanSphincs.Security.Graph.freshPositions_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.freshPositions_tail

/-- info: 'LeanSphincs.Security.Graph.run_prepare_eq_sample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.run_prepare_eq_sample

/-- info: 'LeanSphincs.Security.Graph.replayPrepare_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.replayPrepare_congr

/-- info: 'LeanSphincs.Security.Graph.replayPrepare_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.replayPrepare_update

/-- info: 'LeanSphincs.Security.Graph.evalDist_samplePrepare_eq_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.evalDist_samplePrepare_eq_uniform

/-- info: 'LeanSphincs.Security.Graph.evalDist_prepare_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.evalDist_prepare_uniform

/-- info: 'LeanSphincs.Security.Graph.replayPrepare_eq_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.replayPrepare_eq_program

/-- info: 'LeanSphincs.Security.Graph.evalDist_prepare_programmed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.evalDist_prepare_programmed

/-- info: 'LeanSphincs.Security.Graph.evalDist_activeGraph_programmed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.evalDist_activeGraph_programmed

/-- info: 'LeanSphincs.Security.Graph.evalDist_graph_continuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Graph.evalDist_graph_continuation

/-- info: 'LeanSphincs.Lifetime.digestRectangle_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.digestRectangle_card_le

/-- info: 'LeanSphincs.Lifetime.probEvent_inRectangle_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_inRectangle_le

/-- info: 'LeanSphincs.Lifetime.rectangle_exponential_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.rectangle_exponential_bound

/-- info: 'LeanSphincs.Lifetime.adaptive_rectangle_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.adaptive_rectangle_tail

/-- info: 'LeanSphincs.Lifetime.rectangle_union_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.rectangle_union_bound

/-- info: 'LeanSphincs.Lifetime.localizedBankGain_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.localizedBankGain_le

/-- info: 'LeanSphincs.Lifetime.localizedBankGain_square_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.localizedBankGain_square_le

/-- info: 'LeanSphincs.Lifetime.expected_futureBankGain_square_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_futureBankGain_square_le

/-- info: 'LeanSphincs.Lifetime.priorPivotalPositions_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.priorPivotalPositions_card_le

/-- info: 'LeanSphincs.Lifetime.priorPivotalPositions_card_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.priorPivotalPositions_card_zero

/-- info: 'LeanSphincs.Lifetime.priorFunctionCovered_reindex_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.priorFunctionCovered_reindex_iff

/-- info: 'LeanSphincs.Lifetime.priorPivotalPosition_reindex_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.priorPivotalPosition_reindex_iff

/-- info: 'LeanSphincs.Lifetime.probEvent_priorPivotal_position_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_priorPivotal_position_eq

/-- info: 'LeanSphincs.Lifetime.probEvent_priorPivotal_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_priorPivotal_mul_le

/-- info: 'LeanSphincs.Lifetime.priorPivotalPosition_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.priorPivotalPosition_zero_iff

/-- info: 'LeanSphincs.Lifetime.priorFunctionCovered_ofFn_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.priorFunctionCovered_ofFn_iff

/-- info: 'LeanSphincs.Lifetime.probEvent_uniformDisclosureSet_prior_function' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_uniformDisclosureSet_prior_function

/-- info: 'LeanSphincs.Lifetime.probEvent_priorPivotal_zero_gain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_priorPivotal_zero_gain

/-- info: 'LeanSphincs.Lifetime.independentGainMean_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.independentGainMean_mul_le

/-- info: 'LeanSphincs.Lifetime.independentGainMean_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.independentGainMean_le

/-- info: 'LeanSphincs.Lifetime.weighted_independentGainMean_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.weighted_independentGainMean_mul_le

/-- info: 'LeanSphincs.Lifetime.centeredGain_telescope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.centeredGain_telescope

/-- info: 'LeanSphincs.Lifetime.actualGainSum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.actualGainSum_le

/-- info: 'LeanSphincs.Lifetime.actualGainSum_occupation_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.actualGainSum_occupation_le

/-- info: 'LeanSphincs.Lifetime.actualGainSum_harmonic_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.actualGainSum_harmonic_le

/-- info: 'LeanSphincs.Lifetime.forsBound_le_of_reserveCertificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.forsBound_le_of_reserveCertificate

/-- info: 'LeanSphincs.Lifetime.reserveCertificate_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.reserveCertificate_full

/-- info: 'LeanSphincs.Lifetime.reserveCertificate_pruned20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.reserveCertificate_pruned20

/-- info: 'LeanSphincs.Lifetime.reserveCertificate_pruned13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.reserveCertificate_pruned13

/-- info: 'LeanSphincs.Lifetime.reserveCertificate_pruned14' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.reserveCertificate_pruned14

/-- info: 'LeanSphincs.Lifetime.reserveCertificate_pruned12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.reserveCertificate_pruned12

/-- info: 'LeanSphincs.Lifetime.reserveCertificate_pruned10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.reserveCertificate_pruned10

/-- info: 'LeanSphincs.Lifetime.requested_fors_reserve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.requested_fors_reserve

/-- info: 'LeanSphincs.Lifetime.requested_bootstrap_coefficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.requested_bootstrap_coefficient

/-- info: 'LeanSphincs.Lifetime.normalized_bootstrap_closes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.normalized_bootstrap_closes

/-- info: 'LeanSphincs.Security.ExponentialCharge.traceRun_pure' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.ExponentialCharge.traceRun_pure

/-- info: 'LeanSphincs.Security.ExponentialCharge.traceRun_query_bind' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.ExponentialCharge.traceRun_query_bind

/-- info: 'LeanSphincs.Security.ExponentialCharge.run_eq_trace_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.ExponentialCharge.run_eq_trace_map

/-- info: 'LeanSphincs.Security.ExponentialCharge.traceRun_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.ExponentialCharge.traceRun_erase

/-- info: 'LeanSphincs.Lifetime.expected_bool_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_bool_pow

/-- info: 'LeanSphincs.Lifetime.paired_query_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.paired_query_moment

/-- info: 'LeanSphincs.Lifetime.evalDist_paired_monitor_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.evalDist_paired_monitor_output

/-- info: 'LeanSphincs.Lifetime.paired_monitor_hash_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.paired_monitor_hash_bound

/-- info: 'LeanSphincs.Lifetime.paired_monitor_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.paired_monitor_normalized

/-- info: 'LeanSphincs.Lifetime.paired_monitor_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.paired_monitor_tail

/-- info: 'LeanSphincs.Lifetime.paired_trace_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.paired_trace_tail

/-- info: 'LeanSphincs.Lifetime.paired_trace_family_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.paired_trace_family_tail

/-- info: 'LeanSphincs.Lifetime.recordHit_eq_freshCandidateRecord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.recordHit_eq_freshCandidateRecord

/-- info: 'LeanSphincs.Lifetime.traceHits_eq_freshCandidateTrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.traceHits_eq_freshCandidateTrace

/-- info: 'LeanSphincs.Lifetime.paired_trace_rectangle_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.paired_trace_rectangle_tail

/-- info: 'LeanSphincs.Lifetime.paired_trace_rectangles_negligible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.paired_trace_rectangles_negligible

/-- info: 'LeanSphincs.Lifetime.KnownPair.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.KnownPair.mono

/-- info: 'LeanSphincs.Lifetime.PairedCache.known_of_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.PairedCache.known_of_cached

/-- info: 'LeanSphincs.Lifetime.cachedPairDigest_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.cachedPairDigest_mono

/-- info: 'LeanSphincs.Lifetime.pairedHash_support_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pairedHash_support_cached

/-- info: 'LeanSphincs.Lifetime.traceRun_support_paired' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.traceRun_support_paired

/-- info: 'LeanSphincs.Lifetime.freshCandidateRecord_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.freshCandidateRecord_sound

/-- info: 'LeanSphincs.Lifetime.traceRun_freshCandidates_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.traceRun_freshCandidates_sound

/-- info: 'LeanSphincs.Lifetime.traceCandidateBank_event_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.traceCandidateBank_event_le

/-- info: 'LeanSphincs.Lifetime.traceCandidateBank_sparse_of_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.traceCandidateBank_sparse_of_trace

/-- info: 'LeanSphincs.Lifetime.probEvent_traceCandidateBank_not_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_traceCandidateBank_not_sparse

/-- info: 'LeanSphincs.Lifetime.pairedHash_candidate_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pairedHash_candidate_unchanged

/-- info: 'LeanSphincs.Lifetime.paired_query_new_candidate_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.paired_query_new_candidate_record

/-- info: 'LeanSphincs.Lifetime.traceRun_cached_candidate_mem_bank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.traceRun_cached_candidate_mem_bank

/-- info: 'LeanSphincs.Lifetime.RectangleBankSparse.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.RectangleBankSparse.mono

/-- info: 'LeanSphincs.Lifetime.traceRun_selected_bank_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.traceRun_selected_bank_sparse

/-- info: 'LeanSphincs.Lifetime.probEvent_selected_bank_not_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_selected_bank_not_sparse

/-- info: 'LeanSphincs.Lifetime.PairedReification.traceProgram_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.PairedReification.traceProgram_pure

/-- info: 'LeanSphincs.Lifetime.PairedReification.traceProgram_query_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.PairedReification.traceProgram_query_bind

/-- info: 'LeanSphincs.Lifetime.PairedReification.run_observedHash_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.PairedReification.run_observedHash_same

/-- info: 'LeanSphincs.Lifetime.PairedReification.run_observedPairedHash_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.PairedReification.run_observedPairedHash_same

/-- info: 'LeanSphincs.Lifetime.PairedReification.run_observedRom_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.PairedReification.run_observedRom_same

/-- info: 'LeanSphincs.Lifetime.PairedReification.run_traceProgram_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.PairedReification.run_traceProgram_same

/-- info: 'LeanSphincs.Lifetime.PairedReification.run'_traceProgram_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.PairedReification.run'_traceProgram_same

/-- info: 'LeanSphincs.Security.HiddenRows.knownAgrees_completion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenRows.knownAgrees_completion

/-- info: 'LeanSphincs.Security.HiddenRows.KnownAgrees.reveal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenRows.KnownAgrees.reveal

/-- info: 'LeanSphincs.Security.HiddenRows.compile_private' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenRows.compile_private

/-- info: 'LeanSphincs.Security.HiddenRows.compile_reveal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenRows.compile_reveal

/-- info: 'LeanSphincs.Security.HiddenRows.compile_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenRows.compile_hash

/-- info: 'LeanSphincs.Security.HiddenRows.stopped_private' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenRows.stopped_private

/-- info: 'LeanSphincs.Security.HiddenRows.stopped_reveal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenRows.stopped_reveal

/-- info: 'LeanSphincs.Security.HiddenRows.stopped_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenRows.stopped_hash

/-- info: 'LeanSphincs.Security.HiddenRows.run_compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenRows.run_compile

/-- info: 'LeanSphincs.Security.HiddenRows.compile_queryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenRows.compile_queryBound

/-- info: 'LeanSphincs.Security.HiddenRows.stoppedExperiment_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenRows.stoppedExperiment_eq

/-- info: 'LeanSphincs.Security.HiddenRows.stopped_hidden_input_bound_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenRows.stopped_hidden_input_bound_charge

/-- info: 'LeanSphincs.Security.HiddenRows.stopped_hidden_input_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenRows.stopped_hidden_input_bound

/-- info: 'LeanSphincs.Security.HiddenGraph.input_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.input_injective

/-- info: 'LeanSphincs.Security.HiddenGraph.parse_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.parse_some_iff

/-- info: 'LeanSphincs.Security.HiddenGraph.parse_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.parse_input

/-- info: 'LeanSphincs.Security.HiddenGraph.answer_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.answer_canonical

/-- info: 'LeanSphincs.Security.HiddenGraph.answer_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.answer_other

/-- info: 'LeanSphincs.Security.HiddenGraph.rowModel_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.rowModel_answer

/-- info: 'LeanSphincs.Security.HiddenGraph.run_compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.run_compile

/-- info: 'LeanSphincs.Security.HiddenGraph.compile_queryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.compile_queryBound

/-- info: 'LeanSphincs.Security.HiddenGraph.stoppedExperiment_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.stoppedExperiment_eq

/-- info: 'LeanSphincs.Security.HiddenGraph.stopped_hidden_input_bound_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.stopped_hidden_input_bound_charge

/-- info: 'LeanSphincs.Security.HiddenGraph.stopped_hidden_input_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.stopped_hidden_input_bound

/-- info: 'LeanSphincs.Security.ReferenceChoice.dummyWord_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.ReferenceChoice.dummyWord_valid

/-- info: 'LeanSphincs.Security.ReferenceChoice.firstEncoding_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.ReferenceChoice.firstEncoding_sound

/-- info: 'LeanSphincs.Security.ReferenceChoice.firstEncoding_none_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.ReferenceChoice.firstEncoding_none_at

/-- info: 'LeanSphincs.Security.ReferenceChoice.word_of_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.ReferenceChoice.word_of_some

/-- info: 'LeanSphincs.Security.ReferenceChoice.word_of_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.ReferenceChoice.word_of_none

/-- info: 'LeanSphincs.Security.ReferenceChoice.word_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.ReferenceChoice.word_valid

/-- info: 'LeanSphincs.Security.ReferenceChoice.target_decodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.ReferenceChoice.target_decodes

/-- info: 'LeanSphincs.Security.ReferenceChoice.same_word_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.ReferenceChoice.same_word_target

/-- info: 'LeanSphincs.Security.ReferenceChoice.none_canonical_encoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.ReferenceChoice.none_canonical_encoding

/-- info: 'LeanSphincs.Security.ReferenceChoice.none_canonical_target_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.ReferenceChoice.none_canonical_target_ne

/-- info: 'LeanSphincs.Security.ReferenceChoice.otsLeaf_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.ReferenceChoice.otsLeaf_classification

/-- info: 'LeanSphincs.Security.ReferenceChoice.chosen_cutoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.ReferenceChoice.chosen_cutoff

/-- info: 'LeanSphincs.Lifetime.signWithSourcesThen_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.signWithSourcesThen_actual

/-- info: 'LeanSphincs.Lifetime.signWithSourcesThen_record_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.signWithSourcesThen_record_shape

/-- info: 'LeanSphincs.Lifetime.signWithSourcesThen_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.signWithSourcesThen_mass

/-- info: 'LeanSphincs.Lifetime.signWithSourcesThen_future_gain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.signWithSourcesThen_future_gain

/-- info: 'LeanSphincs.Lifetime.expected_signWithSourcesThen_centered_gain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_signWithSourcesThen_centered_gain

/-- info: 'LeanSphincs.Lifetime.expected_signWithSourcesThen_digest_weight_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_signWithSourcesThen_digest_weight_le

/-- info: 'LeanSphincs.Lifetime.excludedPrior_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.excludedPrior_subset

/-- info: 'LeanSphincs.Lifetime.sourceExcludedViews_subset_excludedPrior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.sourceExcludedViews_subset_excludedPrior

/-- info: 'LeanSphincs.Lifetime.excludedPrior_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.excludedPrior_cons

/-- info: 'LeanSphincs.Lifetime.signWithSourcesThen_excluded_gain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.signWithSourcesThen_excluded_gain

/-- info: 'LeanSphincs.Lifetime.expected_signWithSourcesThen_excluded_centered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_signWithSourcesThen_excluded_centered

/-- info: 'LeanSphincs.Lifetime.coverageGain_subprior_rectangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.coverageGain_subprior_rectangle

/-- info: 'LeanSphincs.Lifetime.excludedBankGain_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.excludedBankGain_le

/-- info: 'LeanSphincs.Lifetime.excludedBankGain_square_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.excludedBankGain_square_le

/-- info: 'LeanSphincs.Lifetime.missingTrees_nonempty_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.missingTrees_nonempty_iff

/-- info: 'LeanSphincs.Lifetime.coverageGain_missing_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.coverageGain_missing_iff

/-- info: 'LeanSphincs.Lifetime.coordinateFeature_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.coordinateFeature_card

/-- info: 'LeanSphincs.Lifetime.missingTreeWeight_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.missingTreeWeight_sum

/-- info: 'LeanSphincs.Lifetime.probEvent_coverageGain_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_coverageGain_coordinates

/-- info: 'LeanSphincs.Lifetime.futureCoverageGain_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.futureCoverageGain_coordinates

/-- info: 'LeanSphincs.Lifetime.expected_futureCoverageGain_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_futureCoverageGain_coordinates

/-- info: 'LeanSphincs.Lifetime.missingTreeWeight_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.missingTreeWeight_le_one

/-- info: 'LeanSphincs.Lifetime.adaptive_coordinate_mixture_square_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.adaptive_coordinate_mixture_square_le

/-- info: 'LeanSphincs.Lifetime.PairedReification.run_queryTable_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.PairedReification.run_queryTable_known

/-- info: 'LeanSphincs.Lifetime.PairedReification.run'_poolJointProgram_prepared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.PairedReification.run'_poolJointProgram_prepared

/-- info: 'LeanSphincs.Lifetime.PairedReification.evalDist_poolJointRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.PairedReification.evalDist_poolJointRun

/-- info: 'LeanSphincs.Lifetime.PairedReification.probEvent_poolJointRun_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.PairedReification.probEvent_poolJointRun_trace

/-- info: 'LeanSphincs.Lifetime.PairedReification.probEvent_poolJointRun_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.PairedReification.probEvent_poolJointRun_table

/-- info: 'LeanSphincs.Lifetime.PairedReification.probEvent_poolJointRun_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.PairedReification.probEvent_poolJointRun_bad

/-- info: 'LeanSphincs.Lifetime.PairedReification.observedHash_support_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.PairedReification.observedHash_support_agrees

/-- info: 'LeanSphincs.Lifetime.PairedReification.observedPairedHash_support_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.PairedReification.observedPairedHash_support_agrees

/-- info: 'LeanSphincs.Lifetime.PairedReification.observedRom_support_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.PairedReification.observedRom_support_agrees

/-- info: 'LeanSphincs.Lifetime.PairedReification.traceProgram_support_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.PairedReification.traceProgram_support_agrees

/-- info: 'LeanSphincs.Lifetime.PairedReification.prepared_trace_firstPool_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.PairedReification.prepared_trace_firstPool_agrees

/-- info: 'LeanSphincs.Lifetime.PairedReification.poolJointRun_firstPool_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.PairedReification.poolJointRun_firstPool_agrees

/-- info: 'LeanSphincs.Lifetime.poolGrindRandomness_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.poolGrindRandomness_map

/-- info: 'LeanSphincs.Lifetime.poolGrind_support_landed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.poolGrind_support_landed

/-- info: 'LeanSphincs.Lifetime.balanced_poolGrind_index_bound_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.balanced_poolGrind_index_bound_all

/-- info: 'LeanSphincs.Lifetime.indexedSign_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.indexedSign_erase

/-- info: 'LeanSphincs.Lifetime.indexedSign_cache_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.indexedSign_cache_le

/-- info: 'LeanSphincs.Lifetime.prepared_messageDigest_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.prepared_messageDigest_index

/-- info: 'LeanSphincs.Lifetime.indexedSign_prepared_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.indexedSign_prepared_index

/-- info: 'LeanSphincs.Lifetime.indexedSign_prepared_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.indexedSign_prepared_bound

/-- info: 'LeanSphincs.Lifetime.adaptiveIndexTrace_guarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.adaptiveIndexTrace_guarded

/-- info: 'LeanSphincs.Lifetime.adaptiveIndexTrace_tail_of_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.adaptiveIndexTrace_tail_of_invariant

/-- info: 'LeanSphincs.Lifetime.interleavedIndexStep_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.interleavedIndexStep_erase

/-- info: 'LeanSphincs.Lifetime.interleavedIndexStep_cache_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.interleavedIndexStep_cache_le

/-- info: 'LeanSphincs.Lifetime.interleavedIndexStep_prepared_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.interleavedIndexStep_prepared_bound

/-- info: 'LeanSphincs.Lifetime.interleaved_signing_occupancy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.interleaved_signing_occupancy

/-- info: 'LeanSphincs.Lifetime.indexedSignProgram_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.indexedSignProgram_erase

/-- info: 'LeanSphincs.Lifetime.run_indexedSignProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.run_indexedSignProgram

/-- info: 'LeanSphincs.Lifetime.run'_interleavedIndexProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.run'_interleavedIndexProgram

/-- info: 'LeanSphincs.Lifetime.actual_interleaved_signing_occupancy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.actual_interleaved_signing_occupancy

/-- info: 'LeanSphincs.Lifetime.uniformKeptIndex_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.uniformKeptIndex_bound

/-- info: 'LeanSphincs.Lifetime.run'_hybridIndexProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.run'_hybridIndexProgram

/-- info: 'LeanSphincs.Lifetime.prepared_hybrid_occupancy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.prepared_hybrid_occupancy

/-- info: 'LeanSphincs.Lifetime.actual_hybrid_occupancy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.actual_hybrid_occupancy

/-- info: 'LeanSphincs.Lifetime.requested_hybrid_union_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.requested_hybrid_union_budget

/-- info: 'LeanSphincs.Lifetime.actual_hybrid_occupancy_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.actual_hybrid_occupancy_sum

/-- info: 'LeanSphincs.Lifetime.common_hybrid_occupancy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.common_hybrid_occupancy

/-- info: 'LeanSphincs.Lifetime.list_view_count_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.list_view_count_le

/-- info: 'LeanSphincs.Lifetime.viewCap_of_list_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.viewCap_of_list_counts

/-- info: 'LeanSphincs.Security.ReferenceChoice.eval_search' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.ReferenceChoice.eval_search

/-- info: 'LeanSphincs.Security.ReferenceChoice.queriedInputs_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.ReferenceChoice.queriedInputs_encode

/-- info: 'LeanSphincs.Security.ReferenceChoice.search_query_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.ReferenceChoice.search_query_classification

/-- info: 'LeanSphincs.Security.ReferenceChoice.search_targets_empty_or_miss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.ReferenceChoice.search_targets_empty_or_miss

/-- info: 'LeanSphincs.Security.ReferenceChoice.search_cache_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.ReferenceChoice.search_cache_clean

/-- info: 'LeanSphincs.Security.ReferenceChoice.search_support_selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.ReferenceChoice.search_support_selection

/-- info: 'LeanSphincs.Security.SignatureWitness.accepted_chosen_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SignatureWitness.accepted_chosen_classification

/-- info: 'LeanSphincs.Security.SignatureWitness.finishSign_none_iff_selection_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SignatureWitness.finishSign_none_iff_selection_none

/-- info: 'LeanSphincs.Security.SignatureWitness.accepted_after_failed_finishSign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SignatureWitness.accepted_after_failed_finishSign

/-- info: 'LeanSphincs.Security.Wots.contact_hidden_or_output' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Wots.contact_hidden_or_output

/-- info: 'LeanSphincs.Security.Wots.ChainException.hidden_or_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Wots.ChainException.hidden_or_output

/-- info: 'LeanSphincs.Security.Fors.Opening.covered_or_hidden' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Fors.Opening.covered_or_hidden

/-- info: 'LeanSphincs.Security.SignatureWitness.accepted_coverage_or_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SignatureWitness.accepted_coverage_or_query

/-- info: 'LeanSphincs.Security.HiddenGraph.coordinates_outgoing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.coordinates_outgoing

/-- info: 'LeanSphincs.Security.HiddenGraph.coordinates_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.coordinates_input

/-- info: 'LeanSphincs.Security.HiddenGraph.answer_graph_label' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.answer_graph_label

/-- info: 'LeanSphincs.Security.HiddenGraph.programGraphCache_preserves_label' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.programGraphCache_preserves_label

/-- info: 'LeanSphincs.Security.HiddenGraph.programGraphCache_label' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.programGraphCache_label

/-- info: 'LeanSphincs.Security.HiddenGraph.programGraphCache_preserves_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.programGraphCache_preserves_other

/-- info: 'LeanSphincs.Security.HiddenGraph.row_miss_all_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.row_miss_all_inputs

/-- info: 'LeanSphincs.Security.HiddenGraph.programGraphCache_row_miss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.programGraphCache_row_miss

/-- info: 'LeanSphincs.Security.HiddenGraph.programGraphCache_row_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.programGraphCache_row_lookup

/-- info: 'LeanSphincs.Security.HiddenGraph.answer_agrees_programGraphCache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.answer_agrees_programGraphCache

/-- info: 'LeanSphincs.Security.HiddenGraph.coordinateAtCell_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.coordinateAtCell_cell

/-- info: 'LeanSphincs.Security.HiddenGraph.coordinateCell_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.coordinateCell_injective

/-- info: 'LeanSphincs.Security.HiddenGraph.coordinateCell_outgoing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.coordinateCell_outgoing

/-- info: 'LeanSphincs.Security.HiddenGraph.uniform_coordinate_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.uniform_coordinate_rows

/-- info: 'LeanSphincs.Security.HiddenGraph.assemble_coordinate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.assemble_coordinate

/-- info: 'LeanSphincs.Security.HiddenGraph.assemble_remaining' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.assemble_remaining

/-- info: 'LeanSphincs.Security.HiddenGraph.uniform_joined_outputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.uniform_joined_outputs

/-- info: 'LeanSphincs.Security.HiddenGraph.joinedPair_bijective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.joinedPair_bijective

/-- info: 'LeanSphincs.Security.HiddenGraph.uniform_material_graph_outputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.uniform_material_graph_outputs

/-- info: 'LeanSphincs.Security.HiddenGraph.coordinates_joined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.coordinates_joined

/-- info: 'LeanSphincs.Security.HiddenGraph.coordinates_assemble' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.coordinates_assemble

/-- info: 'LeanSphincs.Security.HiddenGraph.highHalves_assemble' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.highHalves_assemble

/-- info: 'LeanSphincs.Security.HiddenGraph.completed_active_label' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.completed_active_label

/-- info: 'LeanSphincs.Security.HiddenGraph.completed_row_outgoing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.completed_row_outgoing

/-- info: 'LeanSphincs.Security.HiddenGraph.completed_row_high' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.completed_row_high

/-- info: 'LeanSphincs.Security.HiddenGraph.completed_pruned_incoming' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.completed_pruned_incoming

/-- info: 'LeanSphincs.Security.HiddenGraph.evalDist_sampleSplitPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.evalDist_sampleSplitPair

/-- info: 'LeanSphincs.Security.HiddenGraph.evalDist_sampleMaterial_graph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.evalDist_sampleMaterial_graph

/-- info: 'LeanSphincs.Security.HiddenGraph.evalDist_material_graph_continuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenGraph.evalDist_material_graph_continuation

/-- info: 'LeanSphincs.Security.GraphView.publicData_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.publicData_correct

/-- info: 'LeanSphincs.Security.GraphView.coordinates_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.coordinates_correct

/-- info: 'LeanSphincs.Security.GraphView.eval_lift_hash' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.eval_lift_hash

/-- info: 'LeanSphincs.Security.GraphView.eval_reveal' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.eval_reveal

/-- info: 'LeanSphincs.Security.GraphView.eval_sequence_reveal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.eval_sequence_reveal

/-- info: 'LeanSphincs.Security.GraphView.eval_finishSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.eval_finishSource

/-- info: 'LeanSphincs.Security.GraphView.eval_finishSign_assembled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.eval_finishSign_assembled

/-- info: 'LeanSphincs.Security.GraphView.finishSource_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.finishSource_correct

/-- info: 'LeanSphincs.Security.GraphView.fixedSource_lift_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.fixedSource_lift_view

/-- info: 'LeanSphincs.Security.GraphView.fixedSource_lift_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.fixedSource_lift_hash

/-- info: 'LeanSphincs.Security.GraphView.fixedSource_lift_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.fixedSource_lift_prob

/-- info: 'LeanSphincs.Security.GraphView.fixed_signSourceLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.fixed_signSourceLoop

/-- info: 'LeanSphincs.Security.GraphView.signSource_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.signSource_correct

/-- info: 'LeanSphincs.Lifetime.activeFutureWeight_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.activeFutureWeight_succ

/-- info: 'LeanSphincs.Lifetime.activeFutureWeight_insert_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.activeFutureWeight_insert_erase

/-- info: 'LeanSphincs.Lifetime.activeIndependentMean_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.activeIndependentMean_mul_le

/-- info: 'LeanSphincs.Lifetime.futureCoverageGain_zero_of_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.futureCoverageGain_zero_of_covered

/-- info: 'LeanSphincs.Lifetime.viewCovered_self_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.viewCovered_self_mem

/-- info: 'LeanSphincs.Lifetime.activeSourceGain_restore_bank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.activeSourceGain_restore_bank

/-- info: 'LeanSphincs.Lifetime.activeBankAfter_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.activeBankAfter_same

/-- info: 'LeanSphincs.Lifetime.signWithSourcesThen_active_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.signWithSourcesThen_active_identity

/-- info: 'LeanSphincs.Lifetime.sum_removedPriorWeight_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.sum_removedPriorWeight_le

/-- info: 'LeanSphincs.Lifetime.expected_pool_removedPriorWeight_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_pool_removedPriorWeight_le

/-- info: 'LeanSphincs.Lifetime.finiteMean_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.finiteMean_const

/-- info: 'LeanSphincs.Lifetime.finiteMean_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.finiteMean_add

/-- info: 'LeanSphincs.Lifetime.finiteMean_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.finiteMean_sub

/-- info: 'LeanSphincs.Lifetime.finiteMean_finsetSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.finiteMean_finsetSum

/-- info: 'LeanSphincs.Lifetime.pairGrandMean_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pairGrandMean_comm

/-- info: 'LeanSphincs.Lifetime.centeredPairKernel_source_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.centeredPairKernel_source_mean

/-- info: 'LeanSphincs.Lifetime.centeredPairKernel_target_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.centeredPairKernel_target_mean

/-- info: 'LeanSphincs.Lifetime.offDiagonalPairIncrement_mean_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.offDiagonalPairIncrement_mean_zero

/-- info: 'LeanSphincs.Lifetime.offDiagonalPairIncrement_second_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.offDiagonalPairIncrement_second_moment

/-- info: 'LeanSphincs.Lifetime.offDiagonalPairIncrement_square_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.offDiagonalPairIncrement_square_le

/-- info: 'LeanSphincs.Lifetime.sourceCenteredPairBank_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.sourceCenteredPairBank_decomposition

/-- info: 'LeanSphincs.Lifetime.sourceProjection_mean_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.sourceProjection_mean_zero

/-- info: 'LeanSphincs.Lifetime.sourceProjection_second_moment_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.sourceProjection_second_moment_le

/-- info: 'LeanSphincs.Lifetime.viewedSign_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.viewedSign_index

/-- info: 'LeanSphincs.Lifetime.viewedSign_landed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.viewedSign_landed

/-- info: 'LeanSphincs.Lifetime.fullViewStep_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fullViewStep_index

/-- info: 'LeanSphincs.Lifetime.fullViewStep_landed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fullViewStep_landed

/-- info: 'LeanSphincs.Lifetime.fullViewTrace_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fullViewTrace_index

/-- info: 'LeanSphincs.Lifetime.fullViewTrace_landed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fullViewTrace_landed

/-- info: 'LeanSphincs.Lifetime.localFullView_index_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.localFullView_index_iff

/-- info: 'LeanSphincs.Lifetime.fullViewLocals_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fullViewLocals_count

/-- info: 'LeanSphincs.Lifetime.fullViewLocals_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fullViewLocals_cap

/-- info: 'LeanSphincs.Lifetime.actual_hybrid_view_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.actual_hybrid_view_overflow

/-- info: 'LeanSphincs.Lifetime.fullViewDisclosure_eq_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fullViewDisclosure_eq_trace

/-- info: 'LeanSphincs.Lifetime.fullViewDisclosure_ideal_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fullViewDisclosure_ideal_suffix

/-- info: 'LeanSphincs.Lifetime.fullViewDisclosure_prefix_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fullViewDisclosure_prefix_suffix

/-- info: 'LeanSphincs.Lifetime.expected_futureOverflow_actual_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_futureOverflow_actual_prefix

/-- info: 'LeanSphincs.Lifetime.expected_futureOverflow_all_prefixes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_futureOverflow_all_prefixes

/-- info: 'LeanSphincs.Lifetime.finiteMean_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.finiteMean_mono

/-- info: 'LeanSphincs.Lifetime.finiteMean_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.finiteMean_mul

/-- info: 'LeanSphincs.Lifetime.finiteMean_pair_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.finiteMean_pair_comm

/-- info: 'LeanSphincs.Lifetime.finiteMean_centered_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.finiteMean_centered_square

/-- info: 'LeanSphincs.Lifetime.finiteMean_centered_square_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.finiteMean_centered_square_le

/-- info: 'LeanSphincs.Lifetime.centeredPairKernel_as_centered_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.centeredPairKernel_as_centered_row

/-- info: 'LeanSphincs.Lifetime.centeredPairKernel_energy_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.centeredPairKernel_energy_le

/-- info: 'LeanSphincs.Lifetime.centeredPairKernel_energy_le_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.centeredPairKernel_energy_le_mean

/-- info: 'LeanSphincs.Lifetime.finiteMean_square_add_centered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.finiteMean_square_add_centered

/-- info: 'LeanSphincs.Lifetime.centered_source_energy_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.centered_source_energy_update

/-- info: 'LeanSphincs.Lifetime.centered_source_energy_update_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.centered_source_energy_update_le

/-- info: 'LeanSphincs.Lifetime.pairProcessStep_centered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pairProcessStep_centered

/-- info: 'LeanSphincs.Lifetime.pairProcessIncrement_mean_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pairProcessIncrement_mean_zero

/-- info: 'LeanSphincs.Lifetime.pairProcessIncrement_square_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pairProcessIncrement_square_le

/-- info: 'LeanSphincs.Lifetime.pairProcessStep_square_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pairProcessStep_square_le

/-- info: 'LeanSphincs.Lifetime.centered_target_energy_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.centered_target_energy_update

/-- info: 'LeanSphincs.Lifetime.pairProcessStep_energy_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pairProcessStep_energy_le

/-- info: 'LeanSphincs.Lifetime.pairProcessStep_potential_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pairProcessStep_potential_le

/-- info: 'LeanSphincs.Lifetime.pairProcessValueMean_le_potential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pairProcessValueMean_le_potential

/-- info: 'LeanSphincs.Lifetime.pairProcessValueMean_zero_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pairProcessValueMean_zero_le

/-- info: 'LeanSphincs.Lifetime.pairedWordJoint_candidate_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pairedWordJoint_candidate_slot

/-- info: 'LeanSphincs.Lifetime.pairedWordJoint_candidate_embedding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pairedWordJoint_candidate_embedding

/-- info: 'LeanSphincs.Lifetime.padDigestWord_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.padDigestWord_nil

/-- info: 'LeanSphincs.Lifetime.evalDist_pairedWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.evalDist_pairedWord

/-- info: 'LeanSphincs.Lifetime.padDigestWord_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.padDigestWord_length

/-- info: 'LeanSphincs.Lifetime.padDigestWord_retains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.padDigestWord_retains

/-- info: 'LeanSphincs.Lifetime.freshDigestWord_length_le_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.freshDigestWord_length_le_cost

/-- info: 'LeanSphincs.Lifetime.paired_trace_source_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.paired_trace_source_cost_le

/-- info: 'LeanSphincs.Lifetime.pairedWordJoint_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pairedWordJoint_word

/-- info: 'LeanSphincs.Lifetime.evalDist_pairedWordJoint_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.evalDist_pairedWordJoint_word

/-- info: 'LeanSphincs.Lifetime.pairedWordJoint_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pairedWordJoint_support

/-- info: 'LeanSphincs.Lifetime.pairedWordJoint_candidate_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pairedWordJoint_candidate_mem

/-- info: 'LeanSphincs.Lifetime.reserveCertificate_full_extra16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.reserveCertificate_full_extra16

/-- info: 'LeanSphincs.Lifetime.reserveCertificate_pruned20_extra16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.reserveCertificate_pruned20_extra16

/-- info: 'LeanSphincs.Lifetime.reserveCertificate_pruned13_extra16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.reserveCertificate_pruned13_extra16

/-- info: 'LeanSphincs.Lifetime.reserveCertificate_pruned14_extra16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.reserveCertificate_pruned14_extra16

/-- info: 'LeanSphincs.Lifetime.reserveCertificate_pruned12_extra16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.reserveCertificate_pruned12_extra16

/-- info: 'LeanSphincs.Lifetime.reserveCertificate_pruned10_extra16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.reserveCertificate_pruned10_extra16

/-- info: 'LeanSphincs.Lifetime.requested_fors_extra16_reserve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.requested_fors_extra16_reserve

/-- info: 'LeanSphincs.Lifetime.markedSourceRatio_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.markedSourceRatio_nonneg

/-- info: 'LeanSphincs.Lifetime.requested_markedSourceRatio_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.requested_markedSourceRatio_le

/-- info: 'LeanSphincs.Lifetime.requested_markedSourceRatio_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.requested_markedSourceRatio_small

/-- info: 'LeanSphincs.Lifetime.requested_markedSourceRatio_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.requested_markedSourceRatio_tail

/-- info: 'LeanSphincs.Lifetime.requested_marked_expansion_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.requested_marked_expansion_budget

/-- info: 'LeanSphincs.Lifetime.viewedSign_disclosures' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.viewedSign_disclosures

/-- info: 'LeanSphincs.Lifetime.signWithSources_viewedSign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.signWithSources_viewedSign

/-- info: 'LeanSphincs.Lifetime.sourceInterleavedStep_views' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.sourceInterleavedStep_views

/-- info: 'LeanSphincs.Lifetime.sourcePrefix_views' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.sourcePrefix_views

/-- info: 'LeanSphincs.Lifetime.expected_futureOverflow_source_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_futureOverflow_source_prefix

/-- info: 'LeanSphincs.Lifetime.expected_futureOverflow_source_all_prefixes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.expected_futureOverflow_source_all_prefixes

/-- info: 'LeanSphincs.Security.GraphView.hashCalls_forsKey_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.hashCalls_forsKey_exact

/-- info: 'LeanSphincs.Security.GraphView.hashCalls_forsOpen_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.hashCalls_forsOpen_exact

/-- info: 'LeanSphincs.Security.GraphView.hashCalls_published_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.hashCalls_published_values

/-- info: 'LeanSphincs.Security.GraphView.hashCalls_otsSignFrom_search' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.hashCalls_otsSignFrom_search

/-- info: 'LeanSphincs.Security.GraphView.hashCalls_treePath_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.hashCalls_treePath_exact

/-- info: 'LeanSphincs.Security.GraphView.hashCalls_signLayer_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.hashCalls_signLayer_exact

/-- info: 'LeanSphincs.Security.GraphView.hashCalls_finishSign_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.hashCalls_finishSign_exact

/-- info: 'LeanSphincs.Security.GraphView.fixedCostSource_lift_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.fixedCostSource_lift_hash

/-- info: 'LeanSphincs.Security.GraphView.fixedCostSource_lift_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.fixedCostSource_lift_prob

/-- info: 'LeanSphincs.Security.GraphView.fixedWorldCost_lift_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.fixedWorldCost_lift_hash

/-- info: 'LeanSphincs.Security.GraphView.fixedCostSource_reveal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.fixedCostSource_reveal

/-- info: 'LeanSphincs.Security.GraphView.fixedCostSource_tick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.fixedCostSource_tick

/-- info: 'LeanSphincs.Security.GraphView.fixedCostSource_sequence_reveal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.fixedCostSource_sequence_reveal

/-- info: 'LeanSphincs.Security.GraphView.fixed_finishCostSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.fixed_finishCostSource

/-- info: 'LeanSphincs.Security.GraphView.finishCostSource_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.finishCostSource_correct

/-- info: 'LeanSphincs.Security.GraphView.fixed_signCostSourceLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.fixed_signCostSourceLoop

/-- info: 'LeanSphincs.Security.GraphView.signCostSource_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.signCostSource_correct

/-- info: 'LeanSphincs.Security.GraphView.fixedCostSource_ordinary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.fixedCostSource_ordinary

/-- info: 'LeanSphincs.Security.GraphView.fixedCostSource_interaction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.fixedCostSource_interaction

/-- info: 'LeanSphincs.Security.GraphView.fixedCostSource_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.fixedCostSource_rest

/-- info: 'LeanSphincs.Security.GraphView.fixedWorldCost_keygen_graph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.fixedWorldCost_keygen_graph

/-- info: 'LeanSphincs.Security.GraphView.costGame_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.GraphView.costGame_correct

/-- info: 'LeanSphincs.Security.HiddenCost.pays_pure' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.pays_pure

/-- info: 'LeanSphincs.Security.HiddenCost.pays_query_bind' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.pays_query_bind

/-- info: 'LeanSphincs.Security.HiddenCost.pays_mono' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.pays_mono

/-- info: 'LeanSphincs.Security.HiddenCost.pays_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.pays_map

/-- info: 'LeanSphincs.Security.HiddenCost.traceCharge_append' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.traceCharge_append

/-- info: 'LeanSphincs.Security.HiddenCost.rowCost_recorded' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.rowCost_recorded

/-- info: 'LeanSphincs.Security.HiddenCost.trace_pays_rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.trace_pays_rows

/-- info: 'LeanSphincs.Security.HiddenCost.erase_pays_rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.erase_pays_rows

/-- info: 'LeanSphincs.Security.HiddenCost.compile_pays_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.compile_pays_rows

/-- info: 'LeanSphincs.Security.HiddenCost.revealComparison_pays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.revealComparison_pays

/-- info: 'LeanSphincs.Security.HiddenCost.comparison_guess_le_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.comparison_guess_le_rows

/-- info: 'LeanSphincs.Security.HiddenCost.common_hidden_input_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.common_hidden_input_bound

/-- info: 'LeanSphincs.Security.HiddenCost.traceCost_append' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.traceCost_append

/-- info: 'LeanSphincs.Security.HiddenCost.recorded_cost' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.recorded_cost

/-- info: 'LeanSphincs.Security.HiddenCost.erase_tick' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.erase_tick

/-- info: 'LeanSphincs.Security.HiddenCost.erase_ordinary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.erase_ordinary

/-- info: 'LeanSphincs.Security.HiddenCost.erase_reveal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.erase_reveal

/-- info: 'LeanSphincs.Security.HiddenCost.trace_pure' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.trace_pure

/-- info: 'LeanSphincs.Security.HiddenCost.trace_query_bind' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.trace_query_bind

/-- info: 'LeanSphincs.Security.HiddenCost.bounded_pure' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.bounded_pure

/-- info: 'LeanSphincs.Security.HiddenCost.bounded_query_bind' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.bounded_query_bind

/-- info: 'LeanSphincs.Security.HiddenCost.cap_bounded' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.cap_bounded

/-- info: 'LeanSphincs.Security.HiddenCost.trace_support_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.trace_support_cost_le

/-- info: 'LeanSphincs.Security.HiddenCost.erase_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.erase_support

/-- info: 'LeanSphincs.Security.HiddenCost.compile_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.compile_support

/-- info: 'LeanSphincs.Security.HiddenCost.revealComparison_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.revealComparison_support

/-- info: 'LeanSphincs.Security.HiddenCost.comparison_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.comparison_cost_le

/-- info: 'LeanSphincs.Security.HiddenCost.capped_comparison_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.capped_comparison_cost_le

/-- info: 'LeanSphincs.Security.HiddenReveal.fixedComparison_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenReveal.fixedComparison_pure

/-- info: 'LeanSphincs.Security.HiddenReveal.fixedComparison_private' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenReveal.fixedComparison_private

/-- info: 'LeanSphincs.Security.HiddenReveal.fixedComparison_reveal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenReveal.fixedComparison_reveal

/-- info: 'LeanSphincs.Security.HiddenReveal.fixedComparison_guess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenReveal.fixedComparison_guess

/-- info: 'LeanSphincs.Security.HiddenReveal.evalDist_completion_fixedComparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenReveal.evalDist_completion_fixedComparison

/-- info: 'LeanSphincs.Security.HiddenOutside.fixedComparison_privateLift_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.fixedComparison_privateLift_bind

/-- info: 'LeanSphincs.Security.HiddenOutside.evalDist_comparison_finite_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.evalDist_comparison_finite_table

/-- info: 'LeanSphincs.Security.HiddenCost.graph_row_seed_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.graph_row_seed_disjoint

/-- info: 'LeanSphincs.Security.HiddenCost.seed_row_entry_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.seed_row_entry_le

/-- info: 'LeanSphincs.Security.HiddenCost.capped_seed_row_allocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.capped_seed_row_allocation

/-- info: 'LeanSphincs.Security.HiddenCost.trace_rate_allocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.trace_rate_allocation

/-- info: 'LeanSphincs.Security.HiddenCost.expected_rate_allocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.expected_rate_allocation

/-- info: 'LeanSphincs.Security.HiddenCost.capped_rate_allocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.capped_rate_allocation

/-- info: 'LeanSphincs.Security.HiddenCost.traceCharge_add_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.traceCharge_add_le

/-- info: 'LeanSphincs.Security.HiddenCost.expectedTraceCharge_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.expectedTraceCharge_add_le

/-- info: 'LeanSphincs.Security.HiddenCost.seed_nonseed_entry_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.seed_nonseed_entry_le

/-- info: 'LeanSphincs.Security.HiddenCost.seedWeight_verifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.seedWeight_verifier

/-- info: 'LeanSphincs.Security.HiddenCost.seedWeight_keygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.seedWeight_keygen

/-- info: 'LeanSphincs.Security.HiddenCost.entry_seed_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.entry_seed_probability

/-- info: 'LeanSphincs.Security.HiddenCost.trace_seed_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.trace_seed_probability

/-- info: 'LeanSphincs.Security.HiddenCost.seed_monitor_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.seed_monitor_bound

/-- info: 'LeanSphincs.Security.HiddenCost.common_seed_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.common_seed_bound

/-- info: 'LeanSphincs.Security.HiddenCost.capped_seed_nonseed_allocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.capped_seed_nonseed_allocation

/-- info: 'LeanSphincs.Security.HiddenOutside.privateLift_pure' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.privateLift_pure

/-- info: 'LeanSphincs.Security.HiddenOutside.privateLift_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.privateLift_bind

/-- info: 'LeanSphincs.Security.HiddenOutside.run_privateLift_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.run_privateLift_bind

/-- info: 'LeanSphincs.Security.HiddenOutside.compile_private' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.compile_private

/-- info: 'LeanSphincs.Security.HiddenOutside.compile_reveal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.compile_reveal

/-- info: 'LeanSphincs.Security.HiddenOutside.compile_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.compile_hash

/-- info: 'LeanSphincs.Security.HiddenOutside.run_compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.run_compile

/-- info: 'LeanSphincs.Security.HiddenOutside.stoppedExperiment_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.stoppedExperiment_eq

/-- info: 'LeanSphincs.Security.HiddenOutside.stop_or_bad_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.stop_or_bad_bound

/-- info: 'LeanSphincs.Security.HiddenOutside.privateLift_pays_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.privateLift_pays_bind

/-- info: 'LeanSphincs.Security.HiddenOutside.compile_pays_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.compile_pays_rows

/-- info: 'LeanSphincs.Security.HiddenOutside.compile_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.compile_support

/-- info: 'LeanSphincs.Security.HiddenOutside.comparison_guess_le_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.comparison_guess_le_rows

/-- info: 'LeanSphincs.Security.HiddenOutside.comparison_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.comparison_cost_le

/-- info: 'LeanSphincs.Security.HiddenOutside.capped_comparison_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.capped_comparison_cost_le

/-- info: 'LeanSphincs.Security.HiddenOutside.common_stop_or_bad_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.common_stop_or_bad_bound

/-- info: 'LeanSphincs.Security.HiddenOutside.common_seed_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.common_seed_bound

/-- info: 'LeanSphincs.Security.HiddenOutside.capped_rate_allocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.capped_rate_allocation

/-- info: 'LeanSphincs.Security.HiddenOutside.runRaw_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.runRaw_pure

/-- info: 'LeanSphincs.Security.HiddenOutside.runRaw_private' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.runRaw_private

/-- info: 'LeanSphincs.Security.HiddenOutside.runRaw_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.runRaw_hash

/-- info: 'LeanSphincs.Security.HiddenOutside.runRaw_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.runRaw_map

/-- info: 'LeanSphincs.Security.HiddenOutside.program_private' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.program_private

/-- info: 'LeanSphincs.Security.HiddenOutside.program_reveal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.program_reveal

/-- info: 'LeanSphincs.Security.HiddenOutside.program_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.program_hash

/-- info: 'LeanSphincs.Security.HiddenOutside.fixedComparison_compile_eq_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.fixedComparison_compile_eq_program

/-- info: 'LeanSphincs.Security.HiddenOutside.evalDist_comparison_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.evalDist_comparison_program

/-- info: 'LeanSphincs.Security.HiddenReveal.risk_private' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenReveal.risk_private

/-- info: 'LeanSphincs.Security.HiddenReveal.risk_reveal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenReveal.risk_reveal

/-- info: 'LeanSphincs.Security.HiddenReveal.risk_guess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenReveal.risk_guess

/-- info: 'LeanSphincs.Security.HiddenReveal.stop_or_bad_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenReveal.stop_or_bad_bound

/-- info: 'LeanSphincs.Security.HiddenCost.common_stop_or_bad_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenCost.common_stop_or_bad_bound

/-- info: 'LeanSphincs.Security.HiddenOutside.instrument_pure' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.instrument_pure

/-- info: 'LeanSphincs.Security.HiddenOutside.instrument_query_bind' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.instrument_query_bind

/-- info: 'LeanSphincs.Security.HiddenOutside.instrument_pays_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.instrument_pays_support

/-- info: 'LeanSphincs.Security.HiddenOutside.runRaw_query_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.runRaw_query_bind

/-- info: 'LeanSphincs.Security.HiddenOutside.runRaw_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.runRaw_support

/-- info: 'LeanSphincs.Security.HiddenOutside.weightedRun_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.weightedRun_pure

/-- info: 'LeanSphincs.Security.HiddenOutside.weightedRun_query_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.weightedRun_query_bind

/-- info: 'LeanSphincs.Security.HiddenOutside.weightedRun_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.weightedRun_value

/-- info: 'LeanSphincs.Security.HiddenOutside.expectedOutputCost_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.expectedOutputCost_pure

/-- info: 'LeanSphincs.Security.HiddenOutside.expectedOutputCost_query_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.expectedOutputCost_query_bind

/-- info: 'LeanSphincs.Security.HiddenOutside.expectedOutputCost_le_credit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.expectedOutputCost_le_credit

/-- info: 'LeanSphincs.Security.HiddenOutside.local_output_query_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.local_output_query_bound

/-- info: 'LeanSphincs.Security.HiddenOutside.local_output_step_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.local_output_step_bound

/-- info: 'LeanSphincs.Security.HiddenOutside.weighted_output_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.weighted_output_bound

/-- info: 'LeanSphincs.Security.HiddenOutside.output_bound_credit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.output_bound_credit

/-- info: 'LeanSphincs.Security.Short.Only.pure'' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.Only.pure'

/-- info: 'LeanSphincs.Security.Short.Only.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.Only.bind

/-- info: 'LeanSphincs.Security.Short.Only.map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.Only.map

/-- info: 'LeanSphincs.Security.Short.Only.ite' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.Only.ite

/-- info: 'LeanSphincs.Security.Short.Only.query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.Only.query

/-- info: 'LeanSphincs.Security.Short.fieldBytes_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.fieldBytes_length

/-- info: 'LeanSphincs.Security.Short.tweakableHashInput_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.tweakableHashInput_length

/-- info: 'LeanSphincs.Security.Short.keygenHashInput_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.keygenHashInput_length

/-- info: 'LeanSphincs.Security.Short.Only.tweakableHash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.Only.tweakableHash

/-- info: 'LeanSphincs.Security.Short.Only.deriveKey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.Only.deriveKey

/-- info: 'LeanSphincs.Security.Short.Only.sequenceFin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.Only.sequenceFin

/-- info: 'LeanSphincs.Security.Short.bytes16_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.bytes16_length

/-- info: 'LeanSphincs.Security.Short.nodePayload_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.nodePayload_length

/-- info: 'LeanSphincs.Security.Short.flatMap_bytes_length'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.flatMap_bytes_length'

/-- info: 'LeanSphincs.Security.Short.flatMap_bytes_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.flatMap_bytes_length

/-- info: 'LeanSphincs.Security.Short.leafPayload_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.leafPayload_length

/-- info: 'LeanSphincs.Security.Short.ftsRootsPayload_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.ftsRootsPayload_length

/-- info: 'LeanSphincs.Security.Short.messageDigestPayload_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.messageDigestPayload_length

/-- info: 'LeanSphincs.Security.Short.Only.chainWalk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.Only.chainWalk

/-- info: 'LeanSphincs.Security.Short.Only.leafHash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.Only.leafHash

/-- info: 'LeanSphincs.Security.Short.Only.encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.Only.encode

/-- info: 'LeanSphincs.Security.Short.Only.otsLeaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.Only.otsLeaf

/-- info: 'LeanSphincs.Security.Short.Only.treeFold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.Only.treeFold

/-- info: 'LeanSphincs.Security.Short.Only.ftsFold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.Only.ftsFold

/-- info: 'LeanSphincs.Security.Short.Only.ftsRecover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.Only.ftsRecover

/-- info: 'LeanSphincs.Security.Short.Only.messageDigestCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.Only.messageDigestCall

/-- info: 'LeanSphincs.Security.Short.Only.messageDigest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.Only.messageDigest

/-- info: 'LeanSphincs.Security.Short.Only.verify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.Only.verify

/-- info: 'LeanSphincs.Security.Short.Seeded.Only.oneTimePublicKey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.Seeded.Only.oneTimePublicKey

/-- info: 'LeanSphincs.Security.Short.Seeded.Only.otsSignFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.Seeded.Only.otsSignFrom

/-- info: 'LeanSphincs.Security.Short.Seeded.Only.treeNode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.Seeded.Only.treeNode

/-- info: 'LeanSphincs.Security.Short.Seeded.Only.ftsNode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.Seeded.Only.ftsNode

/-- info: 'LeanSphincs.Security.Short.Seeded.Only.ftsKey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.Seeded.Only.ftsKey

/-- info: 'LeanSphincs.Security.Short.Seeded.Only.ftsOpen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.Seeded.Only.ftsOpen

/-- info: 'LeanSphincs.Security.Short.Seeded.Only.surrogate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.Seeded.Only.surrogate

/-- info: 'LeanSphincs.Security.Short.Seeded.Only.spineNode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.Seeded.Only.spineNode

/-- info: 'LeanSphincs.Security.Short.Seeded.Only.treeRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.Seeded.Only.treeRoot

/-- info: 'LeanSphincs.Security.Short.Seeded.Only.treePath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.Seeded.Only.treePath

/-- info: 'LeanSphincs.Security.Short.Seeded.Only.keygenFromSeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.Seeded.Only.keygenFromSeed

/-- info: 'LeanSphincs.Security.Short.Seeded.Only.signAttempt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.Seeded.Only.signAttempt

/-- info: 'LeanSphincs.Security.Short.Seeded.Only.signLayer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.Seeded.Only.signLayer

/-- info: 'LeanSphincs.Security.Short.Only.finishSign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Short.Only.finishSign

/-- info: 'LeanSphincs.Security.Internalize.OnlyW.pure'' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.OnlyW.pure'

/-- info: 'LeanSphincs.Security.Internalize.OnlyW.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.OnlyW.bind

/-- info: 'LeanSphincs.Security.Internalize.OnlyW.map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.OnlyW.map

/-- info: 'LeanSphincs.Security.Internalize.OnlyW.liftHash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.OnlyW.liftHash

/-- info: 'LeanSphincs.Security.Internalize.OnlyW.liftProb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.OnlyW.liftProb

/-- info: 'LeanSphincs.Security.Internalize.count2_query_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.count2_query_bind

/-- info: 'LeanSphincs.Security.Internalize.count2_pure' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.count2_pure

/-- info: 'LeanSphincs.Security.Internalize.countHashQueries_eq_count2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.countHashQueries_eq_count2

/-- info: 'LeanSphincs.Security.Internalize.bind_map_congr'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.bind_map_congr'

/-- info: 'LeanSphincs.Security.Internalize.merge_cacheQuery_short' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.merge_cacheQuery_short

/-- info: 'LeanSphincs.Security.Internalize.merge_cacheQuery_long' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.merge_cacheQuery_long

/-- info: 'LeanSphincs.Security.Internalize.run_count2_short' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.run_count2_short

/-- info: 'LeanSphincs.Security.Internalize.countShort_eq_count2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.countShort_eq_count2

/-- info: 'LeanSphincs.Security.Internalize.leftRun_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.leftRun_bind

/-- info: 'LeanSphincs.Security.Internalize.rightRun_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.rightRun_bind

/-- info: 'LeanSphincs.Security.Internalize.leftRun_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.leftRun_map

/-- info: 'LeanSphincs.Security.Internalize.rightRun_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.rightRun_map

/-- info: 'LeanSphincs.Security.Internalize.leftRun_short' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.leftRun_short

/-- info: 'LeanSphincs.Security.Internalize.evalDist_bind_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.evalDist_bind_rel

/-- info: 'LeanSphincs.Security.Internalize.evalDist_map_congr_of_evalDist_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.evalDist_map_congr_of_evalDist_eq

/-- info: 'LeanSphincs.Security.Internalize.evalDist_map_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.evalDist_map_rel

/-- info: 'LeanSphincs.Security.Internalize.leftProg_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.leftProg_bind

/-- info: 'LeanSphincs.Security.Internalize.rightProg_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.rightProg_bind

/-- info: 'LeanSphincs.Security.Internalize.Block.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.Block.bind

/-- info: 'LeanSphincs.Security.Internalize.Block.pure'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.Block.pure'

/-- info: 'LeanSphincs.Security.Internalize.rightProg_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.rightProg_forward

/-- info: 'LeanSphincs.Security.Internalize.Block.forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.Block.forward

/-- info: 'LeanSphincs.Security.Internalize.OnlyW.signDigestLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.OnlyW.signDigestLoop

/-- info: 'LeanSphincs.Security.Internalize.OnlyW.sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.OnlyW.sign

/-- info: 'LeanSphincs.Security.Internalize.OnlyW.queryShort' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.OnlyW.queryShort

/-- info: 'LeanSphincs.Security.Internalize.OnlyW.queryDraw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.OnlyW.queryDraw

/-- info: 'LeanSphincs.Security.Internalize.OnlyW.writerLift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.OnlyW.writerLift

/-- info: 'LeanSphincs.Security.Internalize.Block.draw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.Block.draw

/-- info: 'LeanSphincs.Security.Internalize.Block.short' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.Block.short

/-- info: 'LeanSphincs.Security.Internalize.Block.signing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.Block.signing

/-- info: 'LeanSphincs.Security.Internalize.run_simulateQ_ofLift_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.run_simulateQ_ofLift_writer

/-- info: 'LeanSphincs.Security.Internalize.gameImpl_liftWorld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.gameImpl_liftWorld

/-- info: 'LeanSphincs.Security.Internalize.rightRun_liftProb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.rightRun_liftProb

/-- info: 'LeanSphincs.Security.Internalize.leftRun_longQuery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.leftRun_longQuery

/-- info: 'LeanSphincs.Security.Internalize.Block.long' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.Block.long

/-- info: 'LeanSphincs.Security.Internalize.Block.query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.Block.query

/-- info: 'LeanSphincs.Security.Internalize.block_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.block_all

/-- info: 'LeanSphincs.Security.Internalize.leftProg_internal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.leftProg_internal

/-- info: 'LeanSphincs.Security.Internalize.OnlyW.verifyPart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.OnlyW.verifyPart

/-- info: 'LeanSphincs.Security.Internalize.gameAfterSeed_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.gameAfterSeed_eq

/-- info: 'LeanSphincs.Security.Internalize.rest_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.rest_rel

/-- info: 'LeanSphincs.Security.Internalize.gameAfterSeed_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.gameAfterSeed_rel

/-- info: 'LeanSphincs.Security.Internalize.experiment_eq_rightRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.experiment_eq_rightRun

/-- info: 'LeanSphincs.Security.Internalize.merge_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.merge_empty

/-- info: 'LeanSphincs.Security.Internalize.evalDist_experiment_internalize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.evalDist_experiment_internalize

/-- info: 'LeanSphincs.Security.Internalize.leftRun_eq_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.leftRun_eq_split

/-- info: 'LeanSphincs.Security.Internalize.rightRun_eq_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.rightRun_eq_split

/-- info: 'LeanSphincs.Security.Internalize.forgeAdvantage_internalize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.forgeAdvantage_internalize

/-- info: 'LeanSphincs.Security.Internalize.hashQueryBound_internalize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.hashQueryBound_internalize

/-- info: 'LeanSphincs.Security.Internalize.OnlyAdv.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.OnlyAdv.bind

/-- info: 'LeanSphincs.Security.Internalize.OnlyAdv.map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.OnlyAdv.map

/-- info: 'LeanSphincs.Security.Internalize.OnlyAdv.query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.OnlyAdv.query

/-- info: 'LeanSphincs.Security.Internalize.OnlyAdv.simulateProb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.OnlyAdv.simulateProb

/-- info: 'LeanSphincs.Security.Internalize.OnlyAdv.ofLiftWorld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.OnlyAdv.ofLiftWorld

/-- info: 'LeanSphincs.Security.Internalize.OnlyAdv.liftWorldProb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.OnlyAdv.liftWorldProb

/-- info: 'LeanSphincs.Security.Internalize.OnlyAdv.internal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.OnlyAdv.internal

/-- info: 'LeanSphincs.Security.Internalize.OnlyW.gameImpl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.OnlyW.gameImpl

/-- info: 'LeanSphincs.Security.Internalize.OnlyW.gameCore_internalize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Internalize.OnlyW.gameCore_internalize

/-- info: 'LeanSphincs.Security.Eager.extend_cacheQuery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Eager.extend_cacheQuery

/-- info: 'LeanSphincs.Security.Eager.evalDist_map_bind'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Eager.evalDist_map_bind'

/-- info: 'LeanSphincs.Security.Eager.evalDist_romImpl_eq_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Eager.evalDist_romImpl_eq_table

/-- info: 'LeanSphincs.Security.Assembly.OnlyW.counted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Assembly.OnlyW.counted

/-- info: 'LeanSphincs.Security.Assembly.evalDist_simulateQ_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Assembly.evalDist_simulateQ_congr

/-- info: 'LeanSphincs.Security.Assembly.evalDist_fixedRom_eq_fixedHashWorld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Assembly.evalDist_fixedRom_eq_fixedHashWorld

/-- info: 'LeanSphincs.Security.Assembly.OnlyW.gameAfterSeed_internalize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Assembly.OnlyW.gameAfterSeed_internalize

/-- info: 'LeanSphincs.Security.Assembly.evalDist_experiment_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Assembly.evalDist_experiment_fixed

/-- info: 'LeanSphincs.Security.Assembly.extend_cached' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Assembly.extend_cached

/-- info: 'LeanSphincs.Security.Assembly.preparedCache_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Assembly.preparedCache_other

/-- info: 'LeanSphincs.Security.Assembly.preparedCache_parameter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Assembly.preparedCache_parameter

/-- info: 'LeanSphincs.Security.Assembly.preparedCache_secret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Assembly.preparedCache_secret

/-- info: 'LeanSphincs.Security.Assembly.preparedCache_label' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Assembly.preparedCache_label

/-- info: 'LeanSphincs.Security.Assembly.sample_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Assembly.sample_agreement

/-- info: 'LeanSphincs.Security.Assembly.sample_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Assembly.sample_consistent

/-- info: 'LeanSphincs.Security.Assembly.sample_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Assembly.sample_boundary

/-- info: 'LeanSphincs.Security.Assembly.sample_parameter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Assembly.sample_parameter

/-- info: 'LeanSphincs.Security.Assembly.fixedHashWorld_countHashQueries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Assembly.fixedHashWorld_countHashQueries

/-- info: 'LeanSphincs.Security.Assembly.sample_costGame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Assembly.sample_costGame

/-- info: 'LeanSphincs.Security.Stop.costRun_pure' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Stop.costRun_pure

/-- info: 'LeanSphincs.Security.Stop.costRun_query_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Stop.costRun_query_bind

/-- info: 'LeanSphincs.Security.Stop.run_withAddCost_trace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Stop.run_withAddCost_trace

/-- info: 'LeanSphincs.Security.Stop.liftM_id_pmf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Stop.liftM_id_pmf

/-- info: 'LeanSphincs.Security.Stop.evalDist_liftM_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Stop.evalDist_liftM_id

/-- info: 'LeanSphincs.Security.Stop.evalDist_fixedCostSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Stop.evalDist_fixedCostSource

/-- info: 'LeanSphincs.Security.Stop.hits_append_recorded' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Stop.hits_append_recorded

/-- info: 'LeanSphincs.Security.Stop.probEvent_costRun_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Stop.probEvent_costRun_le

/-- info: 'LeanSphincs.Security.Stop.cap_pure'' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Stop.cap_pure'

/-- info: 'LeanSphincs.Security.Stop.cap_query_bind'' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Stop.cap_query_bind'

/-- info: 'LeanSphincs.Security.Stop.probEvent_costRun_le_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Stop.probEvent_costRun_le_cap

/-- info: 'LeanSphincs.Security.Reduce.programGraphCache_congr_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Reduce.programGraphCache_congr_base

/-- info: 'LeanSphincs.Security.Reduce.sampleFn_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Reduce.sampleFn_agree

/-- info: 'LeanSphincs.Security.Reduce.sampleCoordinates_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Reduce.sampleCoordinates_eq

/-- info: 'LeanSphincs.Security.Reduce.costRun_cap_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Reduce.costRun_cap_cost_le

/-- info: 'LeanSphincs.Security.Reduce.sample_costRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Reduce.sample_costRun

/-- info: 'LeanSphincs.Security.Reduce.per_sample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Reduce.per_sample

/-- info: 'LeanSphincs.Security.Reduce.probEvent_bind_le_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Reduce.probEvent_bind_le_add

/-- info: 'LeanSphincs.Security.Reduce.traceCharge_seed_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Reduce.traceCharge_seed_le

/-- info: 'LeanSphincs.Security.Reduce.seed_hit_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Reduce.seed_hit_le

/-- info: 'LeanSphincs.Security.Reduce.probEvent_bind_le_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Reduce.probEvent_bind_le_of

/-- info: 'LeanSphincs.Security.Reduce.probEvent_bind_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Reduce.probEvent_bind_mono

/-- info: 'LeanSphincs.Security.Reduce.forgeAdvantage_le_seedFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Reduce.forgeAdvantage_le_seedFree

/-- info: 'LeanSphincs.Security.HiddenBridge.stopped_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.stopped_map

/-- info: 'LeanSphincs.Security.HiddenBridge.probEvent_stopOr_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.probEvent_stopOr_map

/-- info: 'LeanSphincs.Security.HiddenBridge.erase_trace_query_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.erase_trace_query_bind

/-- info: 'LeanSphincs.Security.HiddenBridge.costRun_le_stopped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.costRun_le_stopped

/-- info: 'LeanSphincs.Security.HiddenBridge.address_isRow' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.address_isRow

/-- info: 'LeanSphincs.Security.HiddenBridge.programGraphCache_empty_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.programGraphCache_empty_some

/-- info: 'LeanSphincs.Security.HiddenBridge.programGraphCache_empty_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.programGraphCache_empty_none

/-- info: 'LeanSphincs.Security.HiddenBridge.graphFn_eq_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.graphFn_eq_answer

/-- info: 'LeanSphincs.Security.HiddenBridge.coordinateAtCell_of_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.coordinateAtCell_of_cell

/-- info: 'LeanSphincs.Security.HiddenBridge.cellKnown_of_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.cellKnown_of_none

/-- info: 'LeanSphincs.Security.HiddenBridge.cellKnown_struct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.cellKnown_struct

/-- info: 'LeanSphincs.Security.HiddenBridge.cellKnown_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.cellKnown_last

/-- info: 'LeanSphincs.Security.HiddenBridge.cellKnown_ftsLeaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.cellKnown_ftsLeaf

/-- info: 'LeanSphincs.Security.HiddenBridge.cellKnown_surrogate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.cellKnown_surrogate

/-- info: 'LeanSphincs.Security.HiddenBridge.cellKnown_children' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.cellKnown_children

/-- info: 'LeanSphincs.Security.HiddenBridge.assemble_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.assemble_agree

/-- info: 'LeanSphincs.Security.HiddenBridge.splitMaterial_parameter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.splitMaterial_parameter

/-- info: 'LeanSphincs.Security.HiddenBridge.labelsOf_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.labelsOf_agree

/-- info: 'LeanSphincs.Security.HiddenBridge.cellKnown_nonchain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.cellKnown_nonchain

/-- info: 'LeanSphincs.Security.HiddenBridge.programGraphCache_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.programGraphCache_congr

/-- info: 'LeanSphincs.Security.HiddenBridge.canonicalGraphInput_struct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.canonicalGraphInput_struct

/-- info: 'LeanSphincs.Security.HiddenBridge.structCache_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.structCache_agree

/-- info: 'LeanSphincs.Security.HiddenBridge.publicData_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.publicData_congr

/-- info: 'LeanSphincs.Security.HiddenBridge.publicData_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.publicData_agree

/-- info: 'LeanSphincs.Security.HiddenBridge.highHalves_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.highHalves_split

/-- info: 'LeanSphincs.Security.HiddenBridge.answer_congr_high' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.answer_congr_high

/-- info: 'LeanSphincs.Security.HiddenBridge.known_of_masked' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.known_of_masked

/-- info: 'LeanSphincs.Security.HiddenBridge.mix_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.mix_known

/-- info: 'LeanSphincs.Security.HiddenBridge.masked_mix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.masked_mix

/-- info: 'LeanSphincs.Security.HiddenBridge.graphCoordinates_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.graphCoordinates_split

/-- info: 'LeanSphincs.Security.HiddenBridge.mix_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.mix_agree

/-- info: 'LeanSphincs.Security.HiddenBridge.seedFreeRun_mix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.seedFreeRun_mix

/-- info: 'LeanSphincs.Security.HiddenBridge.swapKnown_involutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.swapKnown_involutive

/-- info: 'LeanSphincs.Security.HiddenBridge.uniform_map_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.uniform_map_fst

/-- info: 'LeanSphincs.Security.HiddenBridge.uniform_mix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.uniform_mix

/-- info: 'LeanSphincs.Security.HiddenBridge.evalDist_uniform_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.evalDist_uniform_congr

/-- info: 'LeanSphincs.Security.HiddenBridge.evalDist_mix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.evalDist_mix

/-- info: 'LeanSphincs.Security.HiddenBridge.evalDist_mix_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.evalDist_mix_bind

/-- info: 'LeanSphincs.Security.HiddenBridge.evalDist_completion_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.evalDist_completion_bind

/-- info: 'LeanSphincs.Security.HiddenBridge.evalDist_seedFree_completion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.evalDist_seedFree_completion

/-- info: 'LeanSphincs.Security.HiddenBridge.probEvent_bind_mono_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.probEvent_bind_mono_support

/-- info: 'LeanSphincs.Security.HiddenBridge.hiddenRun_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.hiddenRun_eq

/-- info: 'LeanSphincs.Security.HiddenBridge.seedFree_le_stopped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.seedFree_le_stopped

/-- info: 'LeanSphincs.Security.HiddenBridge.outside_stopped_private' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.outside_stopped_private

/-- info: 'LeanSphincs.Security.HiddenBridge.outside_stopped_reveal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.outside_stopped_reveal

/-- info: 'LeanSphincs.Security.HiddenBridge.outside_stopped_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.outside_stopped_hash

/-- info: 'LeanSphincs.Security.HiddenBridge.rows_answer_none' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.rows_answer_none

/-- info: 'LeanSphincs.Security.HiddenBridge.rows_answer_match' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.rows_answer_match

/-- info: 'LeanSphincs.Security.HiddenBridge.rows_answer_miss' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.rows_answer_miss

/-- info: 'LeanSphincs.Security.HiddenBridge.extend_cacheQuery'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.extend_cacheQuery'

/-- info: 'LeanSphincs.Security.HiddenBridge.extend_update_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.extend_update_self

/-- info: 'LeanSphincs.Security.HiddenBridge.evalDist_ordinary_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.evalDist_ordinary_step

/-- info: 'LeanSphincs.Security.HiddenBridge.evalDist_stopped_lazy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.evalDist_stopped_lazy

/-- info: 'LeanSphincs.Security.HiddenBridge.OnlyC.pure'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.OnlyC.pure'

/-- info: 'LeanSphincs.Security.HiddenBridge.OnlyC.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.OnlyC.bind

/-- info: 'LeanSphincs.Security.HiddenBridge.OnlyC.map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.OnlyC.map

/-- info: 'LeanSphincs.Security.HiddenBridge.OnlyC.query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.OnlyC.query

/-- info: 'LeanSphincs.Security.HiddenBridge.OnlyC.liftHash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.OnlyC.liftHash

/-- info: 'LeanSphincs.Security.HiddenBridge.OnlyC.liftProb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.OnlyC.liftProb

/-- info: 'LeanSphincs.Security.HiddenBridge.OnlyC.tick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.OnlyC.tick

/-- info: 'LeanSphincs.Security.HiddenBridge.OnlyC.reveal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.OnlyC.reveal

/-- info: 'LeanSphincs.Security.HiddenBridge.OnlyC.sequenceFin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.OnlyC.sequenceFin

/-- info: 'LeanSphincs.Security.HiddenBridge.OnlyC.writerLift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.OnlyC.writerLift

/-- info: 'LeanSphincs.Security.HiddenBridge.Only.search' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.Only.search

/-- info: 'LeanSphincs.Security.HiddenBridge.onlyC_query_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.onlyC_query_bind

/-- info: 'LeanSphincs.Security.HiddenBridge.OnlyC.cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.OnlyC.cap

/-- info: 'LeanSphincs.Security.HiddenBridge.OnlyC.trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.OnlyC.trace

/-- info: 'LeanSphincs.Security.HiddenBridge.OnlyC.erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.OnlyC.erase

/-- info: 'LeanSphincs.Security.HiddenBridge.OnlyC.finishCostSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.OnlyC.finishCostSource

/-- info: 'LeanSphincs.Security.HiddenBridge.OnlyC.signCostSourceLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.OnlyC.signCostSourceLoop

/-- info: 'LeanSphincs.Security.HiddenBridge.OnlyC.signCostSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.OnlyC.signCostSource

/-- info: 'LeanSphincs.Security.HiddenBridge.OnlyC.costInteraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.OnlyC.costInteraction

/-- info: 'LeanSphincs.Security.HiddenBridge.OnlyC.costGame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.OnlyC.costGame

/-- info: 'LeanSphincs.Security.HiddenBridge.evalDist_stoppedExperiment_lazy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.evalDist_stoppedExperiment_lazy

/-- info: 'LeanSphincs.Security.HiddenBridge.probEvent_bind_congr₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.probEvent_bind_congr₂

/-- info: 'LeanSphincs.Security.HiddenBridge.seedFree_le_lazy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.seedFree_le_lazy

/-- info: 'LeanSphincs.Security.HiddenBridge.withReveals_pure' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.withReveals_pure

/-- info: 'LeanSphincs.Security.HiddenBridge.withReveals_query_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.withReveals_query_bind

/-- info: 'LeanSphincs.Security.HiddenBridge.fst_withReveals' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.fst_withReveals

/-- info: 'LeanSphincs.Security.HiddenBridge.cap_query_bind_gen' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.cap_query_bind_gen

/-- info: 'LeanSphincs.Security.HiddenBridge.cap_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.cap_map

/-- info: 'LeanSphincs.Security.HiddenBridge.trace_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.trace_map

/-- info: 'LeanSphincs.Security.HiddenBridge.erase_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.erase_map

/-- info: 'LeanSphincs.Security.HiddenBridge.outside_stopped_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.outside_stopped_map

/-- info: 'LeanSphincs.Security.HiddenBridge.costGame_eq_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.costGame_eq_map

/-- info: 'LeanSphincs.Security.HiddenBridge.cap_costGame_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.cap_costGame_eq

/-- info: 'LeanSphincs.Security.HiddenBridge.forgeAdvantage_le_rich' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.forgeAdvantage_le_rich

/-- info: 'LeanSphincs.Security.HiddenBridge.reach_mono' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.reach_mono

/-- info: 'LeanSphincs.Security.HiddenBridge.costRun_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.costRun_map

/-- info: 'LeanSphincs.Security.HiddenBridge.withReveals_query_bind'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.withReveals_query_bind'

/-- info: 'LeanSphincs.Security.HiddenBridge.outsideRead_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.outsideRead_support

/-- info: 'LeanSphincs.Security.HiddenBridge.erase_trace_withReveals_query_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.erase_trace_withReveals_query_bind

/-- info: 'LeanSphincs.Security.HiddenBridge.mem_support_option_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.mem_support_option_map

/-- info: 'LeanSphincs.Security.HiddenBridge.lazy_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.lazy_support

/-- info: 'LeanSphincs.Security.HiddenBridge.Only.searchAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.Only.searchAll

/-- info: 'LeanSphincs.Security.HiddenBridge.evalDist_eager_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.evalDist_eager_prefix

/-- info: 'LeanSphincs.Security.HiddenBridge.evalDist_stoppedExperiment_prep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.evalDist_stoppedExperiment_prep

/-- info: 'LeanSphincs.Security.HiddenBridge.forgeAdvantage_le_prep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.forgeAdvantage_le_prep

/-- info: 'LeanSphincs.Security.HiddenReveal.run_stopOr_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenReveal.run_stopOr_le

/-- info: 'LeanSphincs.Security.HiddenOutside.table_stop_or_bad_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenOutside.table_stop_or_bad_bound

/-- info: 'LeanSphincs.Security.HiddenBridge.costRun_withReveals_pure' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.costRun_withReveals_pure

/-- info: 'LeanSphincs.Security.HiddenBridge.costRun_withReveals_query_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.costRun_withReveals_query_bind

/-- info: 'LeanSphincs.Security.HiddenBridge.costRun_withReveals_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.costRun_withReveals_bind

/-- info: 'LeanSphincs.Security.HiddenBridge.costRun_withReveals_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.costRun_withReveals_map

/-- info: 'LeanSphincs.Security.HiddenBridge.costRun_withReveals_liftHash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.costRun_withReveals_liftHash

/-- info: 'LeanSphincs.Security.HiddenBridge.costRun_withReveals_liftProb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.costRun_withReveals_liftProb

/-- info: 'LeanSphincs.Security.HiddenBridge.costRun_withReveals_tick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.costRun_withReveals_tick

/-- info: 'LeanSphincs.Security.HiddenBridge.costRun_withReveals_reveal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.costRun_withReveals_reveal

/-- info: 'LeanSphincs.Security.HiddenBridge.costRun_withReveals_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.costRun_withReveals_cap

/-- info: 'LeanSphincs.Security.HiddenBridge.costRun_withReveals_sequenceReveal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.costRun_withReveals_sequenceReveal

/-- info: 'LeanSphincs.Security.HiddenBridge.finish_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.finish_support

/-- info: 'LeanSphincs.Security.HiddenBridge.revealsOf_of_assembled_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.revealsOf_of_assembled_none

/-- info: 'LeanSphincs.Security.HiddenBridge.signLoop_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.signLoop_support

/-- info: 'LeanSphincs.Security.HiddenBridge.sign_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.sign_support

/-- info: 'LeanSphincs.Security.HiddenBridge.logGood_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.logGood_append

/-- info: 'LeanSphincs.Security.HiddenBridge.costRun_withReveals_plainQuery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.costRun_withReveals_plainQuery

/-- info: 'LeanSphincs.Security.HiddenBridge.interaction_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.interaction_support

/-- info: 'LeanSphincs.Security.HiddenBridge.rich_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.rich_support

/-- info: 'LeanSphincs.Security.SignatureWitness.accepted_landed_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SignatureWitness.accepted_landed_classification

/-- info: 'LeanSphincs.Security.SignatureWitness.crossing_boundary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SignatureWitness.crossing_boundary

/-- info: 'LeanSphincs.Security.SignatureWitness.outside_witness_address' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SignatureWitness.outside_witness_address

/-- info: 'LeanSphincs.Security.SignatureWitness.accepted_full_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SignatureWitness.accepted_full_classification

/-- info: 'LeanSphincs.Security.HiddenBridge.active_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.active_hit

/-- info: 'LeanSphincs.Security.HiddenBridge.leafOutput_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.leafOutput_hit

/-- info: 'LeanSphincs.Security.HiddenBridge.chainOutput_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.chainOutput_hit

/-- info: 'LeanSphincs.Security.HiddenBridge.forsException_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.forsException_hit

/-- info: 'LeanSphincs.Security.HiddenBridge.treeHit_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.treeHit_hit

/-- info: 'LeanSphincs.Security.HiddenBridge.encoding_fields_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.encoding_fields_injective

/-- info: 'LeanSphincs.Security.HiddenBridge.encodingAt_encoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.encodingAt_encoding

/-- info: 'LeanSphincs.Security.HiddenBridge.graph_targets_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.graph_targets_subset

/-- info: 'LeanSphincs.Security.HiddenBridge.encoding_positionAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.encoding_positionAt

/-- info: 'LeanSphincs.Security.HiddenBridge.encodingMatch_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.encodingMatch_hit

/-- info: 'LeanSphincs.Security.HiddenBridge.otsSignFrom_firstEncoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.otsSignFrom_firstEncoding

/-- info: 'LeanSphincs.Security.HiddenBridge.honest_counter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.honest_counter

/-- info: 'LeanSphincs.Security.HiddenBridge.mix_agree_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.mix_agree_fixed

/-- info: 'LeanSphincs.Security.HiddenBridge.graphCoordinates_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.graphCoordinates_T

/-- info: 'LeanSphincs.Security.HiddenBridge.publicData_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.publicData_T

/-- info: 'LeanSphincs.Security.HiddenBridge.structCache_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.structCache_T

/-- info: 'LeanSphincs.Security.HiddenBridge.sampleFn_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.sampleFn_answer

/-- info: 'LeanSphincs.Security.HiddenBridge.answer_extend_final' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.answer_extend_final

/-- info: 'LeanSphincs.Security.HiddenBridge.preparation_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.preparation_support

/-- info: 'LeanSphincs.Security.HiddenBridge.OnlyC.withReveals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.OnlyC.withReveals

/-- info: 'LeanSphincs.Security.HiddenBridge.costRun_entries_short' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.costRun_entries_short

/-- info: 'LeanSphincs.Security.HiddenBridge.costRun_withReveals_cap_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.costRun_withReveals_cap_cost

/-- info: 'LeanSphincs.Security.HiddenBridge.ordinary_length_le_cost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.ordinary_length_le_cost

/-- info: 'LeanSphincs.Security.HiddenBridge.exists_seed_avoiding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.exists_seed_avoiding

/-- info: 'LeanSphincs.Security.HiddenBridge.costRun_support_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.costRun_support_congr

/-- info: 'LeanSphincs.Security.HiddenBridge.knownOf_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.knownOf_known

/-- info: 'LeanSphincs.Security.HiddenBridge.reach_ftsSecret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.reach_ftsSecret

/-- info: 'LeanSphincs.Security.HiddenBridge.reach_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.reach_chain

/-- info: 'LeanSphincs.Security.HiddenBridge.lazy_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.lazy_cached

/-- info: 'LeanSphincs.Security.HiddenBridge.firstEncoding_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.firstEncoding_congr

/-- info: 'LeanSphincs.Security.HiddenBridge.digestInputs_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.digestInputs_mem

/-- info: 'LeanSphincs.Security.HiddenBridge.OnlyC.costGameX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.OnlyC.costGameX

/-- info: 'LeanSphincs.Security.HiddenBridge.sampleModel_parse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.sampleModel_parse

/-- info: 'LeanSphincs.Security.HiddenBridge.sampleModel_incoming' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.sampleModel_incoming

/-- info: 'LeanSphincs.Security.HiddenBridge.sampleModel_outgoing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.sampleModel_outgoing

/-- info: 'LeanSphincs.Security.HiddenBridge.canonicalRow_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.canonicalRow_input

/-- info: 'LeanSphincs.Security.HiddenBridge.not_canonicalRow_of_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.not_canonicalRow_of_target

/-- info: 'LeanSphincs.Security.HiddenBridge.parse_tweakable_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.parse_tweakable_none

/-- info: 'LeanSphincs.Security.HiddenBridge.finalFn_unparsed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.finalFn_unparsed

/-- info: 'LeanSphincs.Security.HiddenBridge.encoding_not_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.encoding_not_row

/-- info: 'LeanSphincs.Security.HiddenBridge.message_not_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.message_not_row

/-- info: 'LeanSphincs.Security.HiddenBridge.tweakable_not_seedHit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.tweakable_not_seedHit

/-- info: 'LeanSphincs.Security.HiddenBridge.fullTable_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.fullTable_eq

/-- info: 'LeanSphincs.Security.HiddenBridge.selection_of_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.selection_of_agree

/-- info: 'LeanSphincs.Security.HiddenBridge.cached_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.cached_hit

/-- info: 'LeanSphincs.Security.HiddenBridge.queried_ftsSecret_revealed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.queried_ftsSecret_revealed

/-- info: 'LeanSphincs.Security.HiddenBridge.queried_chain_reach' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.queried_chain_reach

/-- info: 'LeanSphincs.Security.HiddenBridge.revealed_chain_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.revealed_chain_word

/-- info: 'LeanSphincs.Security.HiddenBridge.canonical_signed_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.canonical_signed_eq

/-- info: 'LeanSphincs.Security.HiddenBridge.cachedDigest_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.cachedDigest_eq

/-- info: 'LeanSphincs.Security.HiddenBridge.bad_of_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.bad_of_accepted

/-- info: 'LeanSphincs.Security.HiddenBridge.preferCache_agrees' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.preferCache_agrees

/-- info: 'LeanSphincs.Security.HiddenBridge.encodingInput_short' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.encodingInput_short

/-- info: 'LeanSphincs.Security.HiddenBridge.encoding_preferCache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.encoding_preferCache

/-- info: 'LeanSphincs.Security.HiddenBridge.sampleFn_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.sampleFn_final

/-- info: 'LeanSphincs.Security.HiddenBridge.win_implies_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenBridge.win_implies_bad

/-- info: 'LeanSphincs.Security.HiddenDebt.fixedRun_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.fixedRun_pure

/-- info: 'LeanSphincs.Security.HiddenDebt.fixedRun_query_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.fixedRun_query_bind

/-- info: 'LeanSphincs.Security.HiddenDebt.fixedStep_unparsed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.fixedStep_unparsed

/-- info: 'LeanSphincs.Security.HiddenDebt.fixedStep_guess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.fixedStep_guess

/-- info: 'LeanSphincs.Security.HiddenDebt.fixedStep_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.fixedStep_canonical

/-- info: 'LeanSphincs.Security.HiddenDebt.fixedStep_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.fixedStep_other

/-- info: 'LeanSphincs.Security.HiddenDebt.fixedStep_draw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.fixedStep_draw

/-- info: 'LeanSphincs.Security.HiddenDebt.fixedStep_reveal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.fixedStep_reveal

/-- info: 'LeanSphincs.Security.HiddenDebt.Agrees.cacheQuery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.Agrees.cacheQuery

/-- info: 'LeanSphincs.Security.HiddenDebt.stopped_query_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.stopped_query_bind

/-- info: 'LeanSphincs.Security.HiddenDebt.stoppedStep_unparsed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.stoppedStep_unparsed

/-- info: 'LeanSphincs.Security.HiddenDebt.stoppedStep_stop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.stoppedStep_stop

/-- info: 'LeanSphincs.Security.HiddenDebt.stoppedStep_miss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.stoppedStep_miss

/-- info: 'LeanSphincs.Security.HiddenDebt.stoppedStep_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.stoppedStep_canonical

/-- info: 'LeanSphincs.Security.HiddenDebt.fixedRun_guesses_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.fixedRun_guesses_mono

/-- info: 'LeanSphincs.Security.HiddenDebt.stopped_le_fixedRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.stopped_le_fixedRun

/-- info: 'LeanSphincs.Security.HiddenDebt.lazyRun_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.lazyRun_pure

/-- info: 'LeanSphincs.Security.HiddenDebt.lazyRun_query_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.lazyRun_query_bind

/-- info: 'LeanSphincs.Security.HiddenDebt.lazyStep_draw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.lazyStep_draw

/-- info: 'LeanSphincs.Security.HiddenDebt.lazyStep_reveal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.lazyStep_reveal

/-- info: 'LeanSphincs.Security.HiddenDebt.lazyStep_unparsed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.lazyStep_unparsed

/-- info: 'LeanSphincs.Security.HiddenDebt.lazyStep_guess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.lazyStep_guess

/-- info: 'LeanSphincs.Security.HiddenDebt.lazyStep_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.lazyStep_canonical

/-- info: 'LeanSphincs.Security.HiddenDebt.lazyStep_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.lazyStep_other

/-- info: 'LeanSphincs.Security.HiddenDebt.sampleCoordinate_expose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.sampleCoordinate_expose

/-- info: 'LeanSphincs.Security.HiddenDebt.randomOracle_known_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.randomOracle_known_support

/-- info: 'LeanSphincs.Security.HiddenDebt.withTable_reveal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.withTable_reveal

/-- info: 'LeanSphincs.Security.HiddenDebt.withTable_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.withTable_swap

/-- info: 'LeanSphincs.Security.HiddenDebt.readOutside_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.readOutside_known

/-- info: 'LeanSphincs.Security.HiddenDebt.withTable_fixedRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.withTable_fixedRun

/-- info: 'LeanSphincs.Security.HiddenDebt.card_digest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.card_digest

/-- info: 'LeanSphincs.Security.HiddenDebt.completion_avoid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.completion_avoid

/-- info: 'LeanSphincs.Security.HiddenDebt.debts_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.debts_record

/-- info: 'LeanSphincs.Security.HiddenDebt.debts_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.debts_store

/-- info: 'LeanSphincs.Security.HiddenDebt.debts_expose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.debts_expose

/-- info: 'LeanSphincs.Security.HiddenDebt.fixedHit_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.fixedHit_store

/-- info: 'LeanSphincs.Security.HiddenDebt.fixedHit_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.fixedHit_record

/-- info: 'LeanSphincs.Security.HiddenDebt.fixedHit_expose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.fixedHit_expose

/-- info: 'LeanSphincs.Security.HiddenDebt.space_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.space_eq

/-- info: 'LeanSphincs.Security.HiddenDebt.weight_le_noHit_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.weight_le_noHit_of

/-- info: 'LeanSphincs.Security.HiddenDebt.weight_le_noHit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.weight_le_noHit

/-- info: 'LeanSphincs.Security.HiddenDebt.weight_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.weight_le_one

/-- info: 'LeanSphincs.Security.HiddenDebt.realized_expose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.realized_expose

/-- info: 'LeanSphincs.Security.HiddenDebt.survival_expose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.survival_expose

/-- info: 'LeanSphincs.Security.HiddenDebt.prob_uniform_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.prob_uniform_not_mem

/-- info: 'LeanSphincs.Security.HiddenDebt.weight_expose_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.weight_expose_mean

/-- info: 'LeanSphincs.Security.HiddenDebt.space_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.space_ne_zero

/-- info: 'LeanSphincs.Security.HiddenDebt.space_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.space_ne_top

/-- info: 'LeanSphincs.Security.HiddenDebt.factor_insert_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.factor_insert_mean

/-- info: 'LeanSphincs.Security.HiddenDebt.truncation_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.truncation_mean

/-- info: 'LeanSphincs.Security.HiddenDebt.prob_uniform_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.prob_uniform_mem

/-- info: 'LeanSphincs.Security.HiddenDebt.uniform_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.uniform_split

/-- info: 'LeanSphincs.Security.HiddenDebt.survival_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.survival_split

/-- info: 'LeanSphincs.Security.HiddenDebt.survival_store_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.survival_store_eq

/-- info: 'LeanSphincs.Security.HiddenDebt.realized_store_of_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.realized_store_of_none

/-- info: 'LeanSphincs.Security.HiddenDebt.realized_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.realized_store

/-- info: 'LeanSphincs.Security.HiddenDebt.survival_split'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.survival_split'

/-- info: 'LeanSphincs.Security.HiddenDebt.survival_store_hidden' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.survival_store_hidden

/-- info: 'LeanSphincs.Security.HiddenDebt.tsum_uniform_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.tsum_uniform_const

/-- info: 'LeanSphincs.Security.HiddenDebt.weight_store_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.weight_store_mean

/-- info: 'LeanSphincs.Security.HiddenDebt.spaceReal_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.spaceReal_pos

/-- info: 'LeanSphincs.Security.HiddenDebt.space_eq_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.space_eq_ofReal

/-- info: 'LeanSphincs.Security.HiddenDebt.oneSub_div_space' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.oneSub_div_space

/-- info: 'LeanSphincs.Security.HiddenDebt.budget_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.budget_le_one

/-- info: 'LeanSphincs.Security.HiddenDebt.budget_succ_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.budget_succ_le

/-- info: 'LeanSphincs.Security.HiddenDebt.budget_le_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.budget_le_of_le

/-- info: 'LeanSphincs.Security.HiddenDebt.budget_probe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.budget_probe

/-- info: 'LeanSphincs.Security.HiddenDebt.probeFactor_le_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.probeFactor_le_fresh

/-- info: 'LeanSphincs.Security.HiddenDebt.probeFactor_debt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.probeFactor_debt

/-- info: 'LeanSphincs.Security.HiddenDebt.probeFactor_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.probeFactor_le_one

/-- info: 'LeanSphincs.Security.HiddenDebt.readOutside_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.readOutside_cached

/-- info: 'LeanSphincs.Security.HiddenDebt.readOutside_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.readOutside_fresh

/-- info: 'LeanSphincs.Security.HiddenDebt.initial_none_of_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.initial_none_of_fresh

/-- info: 'LeanSphincs.Security.HiddenDebt.weight_readOutside_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.weight_readOutside_mean

/-- info: 'LeanSphincs.Security.HiddenDebt.readOutside_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.readOutside_support

/-- info: 'LeanSphincs.Security.HiddenDebt.realized_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.realized_record

/-- info: 'LeanSphincs.Security.HiddenDebt.survival_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.survival_record

/-- info: 'LeanSphincs.Security.HiddenDebt.weight_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.weight_record

/-- info: 'LeanSphincs.Security.HiddenDebt.Growth.refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.Growth.refl

/-- info: 'LeanSphincs.Security.HiddenDebt.Growth.trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.Growth.trans

/-- info: 'LeanSphincs.Security.HiddenDebt.growth_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.growth_record

/-- info: 'LeanSphincs.Security.HiddenDebt.growth_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.growth_store

/-- info: 'LeanSphincs.Security.HiddenDebt.prepared_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.prepared_store

/-- info: 'LeanSphincs.Security.HiddenDebt.Inv.same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.Inv.same

/-- info: 'LeanSphincs.Security.HiddenDebt.Inv.expose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.Inv.expose

/-- info: 'LeanSphincs.Security.HiddenDebt.Inv.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.Inv.mono

/-- info: 'LeanSphincs.Security.HiddenDebt.Inv.grow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.Inv.grow

/-- info: 'LeanSphincs.Security.HiddenDebt.one_sub_add_le_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.one_sub_add_le_mul

/-- info: 'LeanSphincs.Security.HiddenDebt.one_sub_sum_le_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.one_sub_sum_le_prod

/-- info: 'LeanSphincs.Security.HiddenDebt.survival_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.survival_ge

/-- info: 'LeanSphincs.Security.HiddenDebt.weight_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.weight_ge

/-- info: 'LeanSphincs.Security.HiddenDebt.monitor_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.monitor_pure

/-- info: 'LeanSphincs.Security.HiddenDebt.monitor_query_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.monitor_query_bind

/-- info: 'LeanSphincs.Security.HiddenDebt.erase_query_bind_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.erase_query_bind_inl

/-- info: 'LeanSphincs.Security.HiddenDebt.erase_query_bind_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.erase_query_bind_inr

/-- info: 'LeanSphincs.Security.HiddenDebt.monitor_project' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.monitor_project

/-- info: 'LeanSphincs.Security.HiddenDebt.sampleCoordinate_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.sampleCoordinate_known

/-- info: 'LeanSphincs.Security.HiddenDebt.sampleCoordinate_unknown' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.sampleCoordinate_unknown

/-- info: 'LeanSphincs.Security.HiddenDebt.meanWeight_sample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.meanWeight_sample

/-- info: 'LeanSphincs.Security.HiddenDebt.meanWeight_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.meanWeight_map

/-- info: 'LeanSphincs.Security.HiddenDebt.meanWeight_readOutside_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.meanWeight_readOutside_none

/-- info: 'LeanSphincs.Security.HiddenDebt.sum_target_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.sum_target_le

/-- info: 'LeanSphincs.Security.HiddenDebt.inv_readOutside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.inv_readOutside

/-- info: 'LeanSphincs.Security.HiddenDebt.inv_readOutside_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.inv_readOutside_none

/-- info: 'LeanSphincs.Security.HiddenDebt.inv_guess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.inv_guess

/-- info: 'LeanSphincs.Security.HiddenDebt.digest_inequality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.digest_inequality

/-- info: 'LeanSphincs.Security.HiddenDebt.probe_inequality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.probe_inequality

/-- info: 'LeanSphincs.Security.HiddenDebt.combine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.combine

/-- info: 'LeanSphincs.Security.HiddenDebt.costStep_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.costStep_inl

/-- info: 'LeanSphincs.Security.HiddenDebt.probeFactor_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.probeFactor_sq_le

/-- info: 'LeanSphincs.Security.HiddenDebt.readOutside_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.readOutside_step

/-- info: 'LeanSphincs.Security.HiddenDebt.step_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.step_good

/-- info: 'LeanSphincs.Security.HiddenDebt.endWeight_query_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.endWeight_query_bind

/-- info: 'LeanSphincs.Security.HiddenDebt.endPayments_query_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.endPayments_query_bind

/-- info: 'LeanSphincs.Security.HiddenDebt.saturation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.saturation

/-- info: 'LeanSphincs.Security.HiddenDebt.hit_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.hit_bound

/-- info: 'LeanSphincs.Security.HiddenDebt.debts_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.debts_start

/-- info: 'LeanSphincs.Security.HiddenDebt.inv_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.inv_start

/-- info: 'LeanSphincs.Security.HiddenDebt.weight_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.weight_start

/-- info: 'LeanSphincs.Security.HiddenDebt.hit_bound_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.hit_bound_start

/-- info: 'LeanSphincs.Security.HiddenDebt.baseline_payment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.baseline_payment

/-- info: 'LeanSphincs.Security.HiddenDebt.one_sub_budget_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.HiddenDebt.one_sub_budget_zero
