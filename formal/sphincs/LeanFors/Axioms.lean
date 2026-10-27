import LeanFors

/-!
Axiom guards. The `#print axioms` below pin the main theorem, the 48 size and cost theorems of
`Configurations` and the theorems the documentation cites. The last command checks
every declaration of every `LeanFors` module (`LeanFors.lean` imports all of them) and fails if
one depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`, such as the
`sorryAx` of `sorry` or the `Lean.ofReduceBool` of `native_decide`.
-/

/-- info: 'LeanFors.requestedSecurity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.requestedSecurity

/-- info: 'LeanFors.Configurations.blake2s_h22_layered_k25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.blake2s_h22_layered_k25

/-- info: 'LeanFors.Configurations.blake2s_h22_pruned_k25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.blake2s_h22_pruned_k25

/-- info: 'LeanFors.Configurations.blake2s_h22_pruned_k26' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.blake2s_h22_pruned_k26

/-- info: 'LeanFors.Configurations.blake2s_h24_layered_k25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.blake2s_h24_layered_k25

/-- info: 'LeanFors.Configurations.blake2s_h24_pruned_k25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.blake2s_h24_pruned_k25

/-- info: 'LeanFors.Configurations.blake2s_h24_pruned_k26' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.blake2s_h24_pruned_k26

/-- info: 'LeanFors.Configurations.blake2s_h26_layered_k25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.blake2s_h26_layered_k25

/-- info: 'LeanFors.Configurations.blake2s_h26_pruned_k25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.blake2s_h26_pruned_k25

/-- info: 'LeanFors.Configurations.blake2s_h26_pruned_k26' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.blake2s_h26_pruned_k26

/-- info: 'LeanFors.Configurations.blake2s_h28_layered_k25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.blake2s_h28_layered_k25

/-- info: 'LeanFors.Configurations.blake2s_h28_pruned_k25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.blake2s_h28_pruned_k25

/-- info: 'LeanFors.Configurations.blake2s_h28_pruned_k26' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.blake2s_h28_pruned_k26

/-- info: 'LeanFors.Configurations.keccak256_h22_layered_k25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.keccak256_h22_layered_k25

/-- info: 'LeanFors.Configurations.keccak256_h22_pruned_k25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.keccak256_h22_pruned_k25

/-- info: 'LeanFors.Configurations.keccak256_h22_pruned_k26' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.keccak256_h22_pruned_k26

/-- info: 'LeanFors.Configurations.keccak256_h24_layered_k25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.keccak256_h24_layered_k25

/-- info: 'LeanFors.Configurations.keccak256_h24_pruned_k25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.keccak256_h24_pruned_k25

/-- info: 'LeanFors.Configurations.keccak256_h24_pruned_k26' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.keccak256_h24_pruned_k26

/-- info: 'LeanFors.Configurations.keccak256_h26_layered_k25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.keccak256_h26_layered_k25

/-- info: 'LeanFors.Configurations.keccak256_h26_pruned_k25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.keccak256_h26_pruned_k25

/-- info: 'LeanFors.Configurations.keccak256_h26_pruned_k26' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.keccak256_h26_pruned_k26

/-- info: 'LeanFors.Configurations.keccak256_h28_layered_k25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.keccak256_h28_layered_k25

/-- info: 'LeanFors.Configurations.keccak256_h28_pruned_k25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.keccak256_h28_pruned_k25

/-- info: 'LeanFors.Configurations.keccak256_h28_pruned_k26' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.keccak256_h28_pruned_k26

/-- info: 'LeanFors.Configurations.sha256_h22_layered_k25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.sha256_h22_layered_k25

/-- info: 'LeanFors.Configurations.sha256_h22_pruned_k25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.sha256_h22_pruned_k25

/-- info: 'LeanFors.Configurations.sha256_h22_pruned_k26' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.sha256_h22_pruned_k26

/-- info: 'LeanFors.Configurations.sha256_h24_layered_k25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.sha256_h24_layered_k25

/-- info: 'LeanFors.Configurations.sha256_h24_pruned_k25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.sha256_h24_pruned_k25

/-- info: 'LeanFors.Configurations.sha256_h24_pruned_k26' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.sha256_h24_pruned_k26

/-- info: 'LeanFors.Configurations.sha256_h26_layered_k25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.sha256_h26_layered_k25

/-- info: 'LeanFors.Configurations.sha256_h26_pruned_k25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.sha256_h26_pruned_k25

/-- info: 'LeanFors.Configurations.sha256_h26_pruned_k26' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.sha256_h26_pruned_k26

/-- info: 'LeanFors.Configurations.sha256_h28_layered_k25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.sha256_h28_layered_k25

/-- info: 'LeanFors.Configurations.sha256_h28_pruned_k25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.sha256_h28_pruned_k25

/-- info: 'LeanFors.Configurations.sha256_h28_pruned_k26' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.sha256_h28_pruned_k26

/-- info: 'LeanFors.Configurations.size_h22_layered_k25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.size_h22_layered_k25

/-- info: 'LeanFors.Configurations.size_h22_pruned_k25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.size_h22_pruned_k25

/-- info: 'LeanFors.Configurations.size_h22_pruned_k26' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.size_h22_pruned_k26

/-- info: 'LeanFors.Configurations.size_h24_layered_k25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.size_h24_layered_k25

/-- info: 'LeanFors.Configurations.size_h24_pruned_k25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.size_h24_pruned_k25

/-- info: 'LeanFors.Configurations.size_h24_pruned_k26' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.size_h24_pruned_k26

/-- info: 'LeanFors.Configurations.size_h26_layered_k25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.size_h26_layered_k25

/-- info: 'LeanFors.Configurations.size_h26_pruned_k25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.size_h26_pruned_k25

/-- info: 'LeanFors.Configurations.size_h26_pruned_k26' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.size_h26_pruned_k26

/-- info: 'LeanFors.Configurations.size_h28_layered_k25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.size_h28_layered_k25

/-- info: 'LeanFors.Configurations.size_h28_pruned_k25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.size_h28_pruned_k25

/-- info: 'LeanFors.Configurations.size_h28_pruned_k26' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Configurations.size_h28_pruned_k26

/-- info: 'LeanFors.Security.ForsPotential.det_bitsFH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Security.ForsPotential.det_bitsFH

/-- info: 'LeanFors.Security.Det.forgeAdvantage_le_seedFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Security.Det.forgeAdvantage_le_seedFree

/-- info: 'LeanFors.Security.Det.evalDist_rtable_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Security.Det.evalDist_rtable_split

/-- info: 'LeanFors.Security.DetValue.avg_advDet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Security.DetValue.avg_advDet

/-- info: 'LeanFors.Security.SeedCoupling.evalDist_prepared_continuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Security.SeedCoupling.evalDist_prepared_continuation

/-- info: 'LeanFors.Security.SignatureWitness.accepted_full_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Security.SignatureWitness.accepted_full_classification

/-- info: 'LeanFors.Security.Fors.recover_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Security.Fors.recover_classification

/-- info: 'LeanFors.Security.HiddenBridge.win_implies_badA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Security.HiddenBridge.win_implies_badA

/-- info: 'LeanFors.Security.Prefix.hashCalls_keygenFromSeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Security.Prefix.hashCalls_keygenFromSeed

/-- info: 'LeanFors.Security.GraphView.hashCalls_finishSign_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Security.GraphView.hashCalls_finishSign_exact

/-- info: 'LeanFors.Security.GraphView.scan_boundW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Security.GraphView.scan_boundW

/-- info: 'LeanFors.LoopWalk.creation_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.LoopWalk.creation_le

/-- info: 'LeanFors.Security.H0.lam_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Security.H0.lam_start

/-- info: 'LeanFors.Security.ForsPotential.sign_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Security.ForsPotential.sign_term

/-- info: 'LeanFors.Security.PrunedGraph.keyActive_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Security.PrunedGraph.keyActive_iff

/-- info: 'LeanFors.Security.ForsPotential.expectedFail_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Security.ForsPotential.expectedFail_le

/-- info: 'LeanFors.Security.verified_layers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Security.verified_layers

/-- info: 'LeanFors.Security.PotentialA.smallRoute_potentialF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Security.PotentialA.smallRoute_potentialF

/-- info: 'LeanFors.Security.ForsPotential.reveal_le_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Security.ForsPotential.reveal_le_all

/-- info: 'LeanFors.Security.ForsPotential.arm_paysF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Security.ForsPotential.arm_paysF

/-- info: 'LeanFors.Security.ForsPotential.sample_boundF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Security.ForsPotential.sample_boundF

/-- info: 'LeanFors.Security.ForsPotential.det_smallF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Security.ForsPotential.det_smallF

/-- info: 'LeanFors.Security.ForsPotential.det_largeW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Security.ForsPotential.det_largeW

/-- info: 'LeanFors.Concrete.fullDigestView_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Concrete.fullDigestView_bijective

/-- info: 'LeanFors.Security.fieldInput_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Security.fieldInput_injective

/-- info: 'LeanFors.Security.hashFields_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Security.hashFields_injective

/-- info: 'LeanFors.walk_iterate_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.walk_iterate_ne

/-- info: 'LeanFors.Completeness.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Completeness.correct

/-- info: 'LeanFors.Completeness.eval_treeFold_pruned_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Completeness.eval_treeFold_pruned_path

/-- info: 'LeanFors.signature_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.signature_size

/-- info: 'LeanFors.Cost.verification_compressions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanFors.Cost.verification_compressions

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Array (Name × Name) := #[]
  for h : i in [0:env.header.moduleNames.size] do
    unless (`LeanFors).isPrefixOf env.header.moduleNames[i] do continue
    for name in env.header.moduleData[i]!.constNames do
      for axiomName in ← collectAxioms name do
        unless allowed.contains axiomName do bad := bad.push (name, axiomName)
  unless bad.isEmpty do
    throwError m!"declarations with axioms outside propext, Classical.choice, Quot.sound: {bad.toList}"
