import LeanForest

/-!
Axiom guards. The `#print axioms` below pin the main theorem, the 40 size and cost theorems of
`Configurations` and the theorems the documentation cites. The last command checks
every declaration of every `LeanForest` module (`LeanForest.lean` imports all of them) and fails if
one depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`, such as the
`sorryAx` of `sorry` or the `Lean.ofReduceBool` of `native_decide`.
-/

/-- info: 'LeanForest.requestedSecurity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.requestedSecurity

/-- info: 'LeanForest.Configurations.blake2s_h20_pruned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.blake2s_h20_pruned

/-- info: 'LeanForest.Configurations.blake2s_h22_pruned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.blake2s_h22_pruned

/-- info: 'LeanForest.Configurations.blake2s_h24_layered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.blake2s_h24_layered

/-- info: 'LeanForest.Configurations.blake2s_h24_layered_t6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.blake2s_h24_layered_t6

/-- info: 'LeanForest.Configurations.blake2s_h24_layered_t7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.blake2s_h24_layered_t7

/-- info: 'LeanForest.Configurations.blake2s_h24_pruned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.blake2s_h24_pruned

/-- info: 'LeanForest.Configurations.blake2s_h26_layered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.blake2s_h26_layered

/-- info: 'LeanForest.Configurations.blake2s_h26_pruned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.blake2s_h26_pruned

/-- info: 'LeanForest.Configurations.blake2s_h28_layered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.blake2s_h28_layered

/-- info: 'LeanForest.Configurations.blake2s_h28_pruned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.blake2s_h28_pruned

/-- info: 'LeanForest.Configurations.keccak256_h20_pruned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.keccak256_h20_pruned

/-- info: 'LeanForest.Configurations.keccak256_h22_pruned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.keccak256_h22_pruned

/-- info: 'LeanForest.Configurations.keccak256_h24_layered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.keccak256_h24_layered

/-- info: 'LeanForest.Configurations.keccak256_h24_layered_t6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.keccak256_h24_layered_t6

/-- info: 'LeanForest.Configurations.keccak256_h24_layered_t7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.keccak256_h24_layered_t7

/-- info: 'LeanForest.Configurations.keccak256_h24_pruned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.keccak256_h24_pruned

/-- info: 'LeanForest.Configurations.keccak256_h26_layered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.keccak256_h26_layered

/-- info: 'LeanForest.Configurations.keccak256_h26_pruned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.keccak256_h26_pruned

/-- info: 'LeanForest.Configurations.keccak256_h28_layered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.keccak256_h28_layered

/-- info: 'LeanForest.Configurations.keccak256_h28_pruned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.keccak256_h28_pruned

/-- info: 'LeanForest.Configurations.sha256_h20_pruned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.sha256_h20_pruned

/-- info: 'LeanForest.Configurations.sha256_h22_pruned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.sha256_h22_pruned

/-- info: 'LeanForest.Configurations.sha256_h24_layered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.sha256_h24_layered

/-- info: 'LeanForest.Configurations.sha256_h24_layered_t6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.sha256_h24_layered_t6

/-- info: 'LeanForest.Configurations.sha256_h24_layered_t7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.sha256_h24_layered_t7

/-- info: 'LeanForest.Configurations.sha256_h24_pruned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.sha256_h24_pruned

/-- info: 'LeanForest.Configurations.sha256_h26_layered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.sha256_h26_layered

/-- info: 'LeanForest.Configurations.sha256_h26_pruned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.sha256_h26_pruned

/-- info: 'LeanForest.Configurations.sha256_h28_layered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.sha256_h28_layered

/-- info: 'LeanForest.Configurations.sha256_h28_pruned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.sha256_h28_pruned

/-- info: 'LeanForest.Configurations.size_h20_pruned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.size_h20_pruned

/-- info: 'LeanForest.Configurations.size_h22_pruned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.size_h22_pruned

/-- info: 'LeanForest.Configurations.size_h24_layered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.size_h24_layered

/-- info: 'LeanForest.Configurations.size_h24_layered_t6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.size_h24_layered_t6

/-- info: 'LeanForest.Configurations.size_h24_layered_t7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.size_h24_layered_t7

/-- info: 'LeanForest.Configurations.size_h24_pruned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.size_h24_pruned

/-- info: 'LeanForest.Configurations.size_h26_layered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.size_h26_layered

/-- info: 'LeanForest.Configurations.size_h26_pruned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.size_h26_pruned

/-- info: 'LeanForest.Configurations.size_h28_layered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.size_h28_layered

/-- info: 'LeanForest.Configurations.size_h28_pruned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Configurations.size_h28_pruned

/-- info: 'LeanForest.Security.ForestPotential.det_bitsFH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Security.ForestPotential.det_bitsFH

/-- info: 'LeanForest.Security.Det.forgeAdvantage_le_seedFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Security.Det.forgeAdvantage_le_seedFree

/-- info: 'LeanForest.Security.Det.evalDist_rtable_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Security.Det.evalDist_rtable_split

/-- info: 'LeanForest.Security.DetValue.avg_advDet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Security.DetValue.avg_advDet

/-- info: 'LeanForest.Security.SeedCoupling.evalDist_prepared_continuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Security.SeedCoupling.evalDist_prepared_continuation

/-- info: 'LeanForest.Security.SignatureWitness.accepted_full_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Security.SignatureWitness.accepted_full_classification

/-- info: 'LeanForest.Security.Forest.recover_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Security.Forest.recover_classification

/-- info: 'LeanForest.Security.HiddenBridge.win_implies_badA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Security.HiddenBridge.win_implies_badA

/-- info: 'LeanForest.Security.Prefix.hashCalls_keygenFromSeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Security.Prefix.hashCalls_keygenFromSeed

/-- info: 'LeanForest.Security.GraphView.hashCalls_finishSign_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Security.GraphView.hashCalls_finishSign_exact

/-- info: 'LeanForest.Security.GraphView.scan_boundW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Security.GraphView.scan_boundW

/-- info: 'LeanForest.LoopWalk.creation_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.LoopWalk.creation_le

/-- info: 'LeanForest.Security.H0.lam_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Security.H0.lam_start

/-- info: 'LeanForest.Security.ForestPotential.sign_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Security.ForestPotential.sign_term

/-- info: 'LeanForest.Security.PrunedGraph.keyActive_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Security.PrunedGraph.keyActive_iff

/-- info: 'LeanForest.Security.ForestPotential.expectedFail_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Security.ForestPotential.expectedFail_le

/-- info: 'LeanForest.Security.verified_layers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Security.verified_layers

/-- info: 'LeanForest.Security.PotentialA.smallRoute_potentialF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Security.PotentialA.smallRoute_potentialF

/-- info: 'LeanForest.Security.ForestPotential.reveal_le_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Security.ForestPotential.reveal_le_all

/-- info: 'LeanForest.Security.ForestPotential.arm_paysF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Security.ForestPotential.arm_paysF

/-- info: 'LeanForest.Security.ForestPotential.sample_boundF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Security.ForestPotential.sample_boundF

/-- info: 'LeanForest.Security.ForestPotential.det_smallF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Security.ForestPotential.det_smallF

/-- info: 'LeanForest.Security.ForestPotential.det_largeW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Security.ForestPotential.det_largeW

/-- info: 'LeanForest.Concrete.fullDigestView_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Concrete.fullDigestView_bijective

/-- info: 'LeanForest.Security.fieldInput_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Security.fieldInput_injective

/-- info: 'LeanForest.Security.hashFields_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Security.hashFields_injective

/-- info: 'LeanForest.walk_iterate_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.walk_iterate_ne

/-- info: 'LeanForest.Completeness.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Completeness.correct

/-- info: 'LeanForest.Completeness.eval_treeFold_pruned_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Completeness.eval_treeFold_pruned_path

/-- info: 'LeanForest.signature_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.signature_size

/-- info: 'LeanForest.Cost.verification_compressions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanForest.Cost.verification_compressions

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Array (Name × Name) := #[]
  for h : i in [0:env.header.moduleNames.size] do
    unless (`LeanForest).isPrefixOf env.header.moduleNames[i] do continue
    for name in env.header.moduleData[i]!.constNames do
      for axiomName in ← collectAxioms name do
        unless allowed.contains axiomName do bad := bad.push (name, axiomName)
  unless bad.isEmpty do
    throwError m!"declarations with axioms outside propext, Classical.choice, Quot.sound: {bad.toList}"
