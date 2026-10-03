import LeanSphincs.SecurityPrefixMaterialView

/-! The selected prepared-secret coordinate is absent from the reconstructed signer's joint
output/cost distribution. Honest internal hash work remains counted even when its values are
replaced by the public frontier computation. -/

open OracleComp OracleSpec

namespace LeanSphincs.Security.Prefix
open Concrete Completeness SeedModel PreparedScheme SphincsSecurity.QueryCap

attribute [local irreducible] encodingAttemptLimit digestAttemptLimit Randomized.finishSign
  Seeded.ftsKey Seeded.ftsOpen chainWalk
set_option backward.isDefEq.respectTransparency false

namespace PublicAgreement

variable {parameter : PublicParameter} {seed : MasterSeed} {left right : QueryImpl HashSpec Id}
    (h : PublicAgreement parameter seed left right)
include h

theorem otsCost (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (attempts counter : Nat) :
    hashCalls left (Seeded.otsSignFrom parameter lay tree leaf seed message attempts counter :
      OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) =
    hashCalls right (Seeded.otsSignFrom parameter lay tree leaf seed message attempts counter :
      OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) := by
  induction attempts generalizing counter with
  | zero => rfl
  | succ attempts ih =>
      simp only [Seeded.otsSignFrom, hashCalls_bind, hashCalls_encode, h.encoding]
      cases evalWithAnswerFn right (encode parameter lay tree leaf message
        (BitVec.ofNat counterBits counter) : OracleComp HashSpec (Option Encoding)) with
      | none => rw [ih]
      | some word =>
          simp only [hashCalls_bind, hashCalls_sequenceFin, hashCalls_deriveKey,
            hashCalls_pure, Nat.add_zero]
          apply congrArg (fun value => 1 + value)
          apply Finset.sum_congr rfl
          intro index _
          have hsteps : 0 + (word index).val ≤ chainLength - 1 := by
            have := (word index).isLt
            omega
          rw [hashCalls_chainWalk _ _ _ _ _ _ _ _ _ hsteps,
            hashCalls_chainWalk _ _ _ _ _ _ _ _ _ hsteps]

variable [Params]

theorem layerCost (sk : Seeded.SecretKey) (index : Index) (lay : Layer)
    (hparameter : sk.parameter = parameter) (hseed : sk.seed = seed) :
    hashCalls left (Seeded.signLayer sk index lay : OracleComp HashSpec (Option (LayerSignature lay))) =
      hashCalls right (Seeded.signLayer sk index lay : OracleComp HashSpec (Option (LayerSignature lay))) := by
  simp only [Seeded.signLayer, Seeded.layerMessage, hashCalls_bind, hparameter, hseed,
    h.forsKey, Seeded.otsSign, h.otsCost, otsSignFrom_eq_firstEncoding, h.firstEncoding_eq]
  rw [hashCalls_ftsKey left right]
  cases firstEncoding right parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
    (evalWithAnswerFn right (Seeded.ftsKey parameter index seed : OracleComp HashSpec Digest))
    encodingAttemptLimit 0 with
  | none => simp only [Option.map_none, hashCalls_pure]
  | some pair =>
      simp only [Option.map_some, hashCalls_bind, hashCalls_pure, Nat.add_zero]
      rw [hashCalls_treePath left right]

theorem finishCost (sk : Seeded.SecretKey) (message : Message) (randomness : Randomness)
    (hparameter : sk.parameter = parameter) (hseed : sk.seed = seed) :
    hashCalls left (Randomized.finishSign sk message randomness) =
      hashCalls right (Randomized.finishSign sk message randomness) := by
  simp only [Randomized.finishSign, hashCalls_bind, hashCalls_messageDigest, hparameter,
    h.digest, hashCalls_sequenceFin, hashCalls_deriveKey, hashCalls_sequenceLayers]
  simp only [hashCalls_ftsOpen left right, h.layerCost sk _ _ hparameter hseed]
  cases evalWithAnswerFn left
    (sequenceLayers fun lay => Seeded.signLayer sk
      (digestIndex (evalWithAnswerFn right
        (messageDigest parameter sk.root message randomness : OracleComp HashSpec MessageDigest))) lay)
  <;> cases evalWithAnswerFn right
    (sequenceLayers fun lay => Seeded.signLayer sk
      (digestIndex (evalWithAnswerFn right
        (messageDigest parameter sk.root message randomness : OracleComp HashSpec MessageDigest))) lay)
  <;> simp only [hashCalls_pure]

theorem signAttempt (sk : Seeded.SecretKey) (message : Message) (randomness : Randomness)
    (hparameter : sk.parameter = parameter) :
    evalWithAnswerFn left (Seeded.signAttempt sk message randomness : OracleComp HashSpec (Option Index)) =
      evalWithAnswerFn right (Seeded.signAttempt sk message randomness : OracleComp HashSpec (Option Index)) := by
  simp only [Seeded.signAttempt, evalWithAnswerFn_bind, hparameter, h.digestCall]
  split <;> rfl

theorem countedDigest (sk : Seeded.SecretKey) (message : Message)
    (hparameter : sk.parameter = parameter) (attempts : Nat) :
    simulateQ (fixedHashWorld left) (counted SourceHash (Randomized.signDigestLoop sk message attempts)) =
      simulateQ (fixedHashWorld right) (counted SourceHash (Randomized.signDigestLoop sk message attempts)) := by
  induction attempts with
  | zero => simp only [Randomized.signDigestLoop, counted_pure, simulateQ_pure]
  | succ attempts ih =>
      simp only [Randomized.signDigestLoop, counted_bind, counted_lift_prob, simulateQ_bind,
        simulateQ_map, fixedHashWorld_counted_lift_hash, hashCalls_signAttempt,
        h.signAttempt sk message _ hparameter, fixedHashWorld_lift_prob left right]
      apply bind_congr
      intro sample
      simp only [← PMF.monad_pure_eq_pure, pure_bind, simulateQ_pure]
      cases evalWithAnswerFn right (Seeded.signAttempt sk message sample.1 :
        OracleComp HashSpec (Option Index)) <;> simp only [counted_pure, simulateQ_pure, ih]

theorem signWithCost (segment : Segment) (hsegment : parameter = segment.parameter)
    (secrets : Secrets) (frontier : Digest) (surrogates : Nat → Digest)
    (sk : Seeded.SecretKey) (message : Message)
    (hparameter : sk.parameter = parameter) (hseed : sk.seed = seed) :
    publicSignWithCost segment left secrets frontier surrogates sk message =
      publicSignWithCost segment right secrets frontier surrogates sk message := by
  simp only [publicSignWithCost, h.countedDigest sk message hparameter,
    h.finishCost sk message _ hparameter hseed, hseed, h.finishSign segment hsegment]

end PublicAgreement

variable [Params]

/-- Both the outside programmed function and the explicit secret table can have their selected
coordinate replaced, without changing the public frontier signer's outputs or original cost. -/
theorem publicSignWithCost_replaceMaterial (segment : Segment) (outside : QueryImpl HashSpec Id)
    (material : Material) (replacement frontier : Digest) (surrogates : Nat → Digest)
    (sk : Seeded.SecretKey) (message : Message)
    (hparameter : parameter material = segment.parameter)
    (hskparameter : sk.parameter = parameter material) :
    publicSignWithCost segment (preparedOracle outside sk.seed (replaceMaterial segment material replacement))
      (materialSecrets (replaceMaterial segment material replacement)) frontier surrogates sk message =
    publicSignWithCost segment (preparedOracle outside sk.seed material) (materialSecrets material)
      frontier surrogates sk message := by
  rw [materialSecrets_replaceMaterial, publicSignWithCost_replaceSecret]
  exact (prepared_replaceMaterial_agreement segment outside material replacement sk.seed).signWithCost
    segment hparameter _ _ _ sk message hskparameter rfl

omit [Params] in
theorem surrogate_replaceMaterial (segment : Segment) (outside : QueryImpl HashSpec Id)
    (material : Material) (replacement : Digest) (seed : MasterSeed) (level : Nat) :
    evalWithAnswerFn (preparedOracle outside seed (replaceMaterial segment material replacement))
      (Seeded.surrogate (parameter material) seed level : OracleComp HashSpec Digest) =
    evalWithAnswerFn (preparedOracle outside seed material)
      (Seeded.surrogate (parameter material) seed level : OracleComp HashSpec Digest) := by
  simp only [Seeded.surrogate]
  split
  next hlevel =>
    have hnew := eval_secret_prepared _ seed (replaceMaterial segment material replacement)
      (preparedOracle_agreement outside seed (replaceMaterial segment material replacement))
      (.inr (.inr ⟨level, hlevel⟩))
    have hold := eval_secret_prepared _ seed material (preparedOracle_agreement outside seed material)
      (.inr (.inr ⟨level, hlevel⟩))
    simp only [replaceMaterial_parameter, secretDomain] at hnew hold
    rw [hnew, hold, replaceMaterial_other segment material replacement _ (by simp)]
  next => simp only [evalWithAnswerFn_pure]

/-- The simulator receives the erased material and the frontier, never the selected low secret. -/
noncomputable def erasedMaterialSign (segment : Segment) (outside : QueryImpl HashSpec Id)
    (material : Material) (frontier root : Digest) (message : Message) : PMF (Option Signature × Nat) :=
  let erased := replaceMaterial segment material 0
  publicSignWithCost segment (preparedOracle outside 0 erased) (materialSecrets erased) frontier
    (fun level => evalWithAnswerFn (preparedOracle outside 0 erased)
      (Seeded.surrogate segment.parameter 0 level : OracleComp HashSpec Digest))
    ⟨0, parameter erased, root⟩ message

theorem erasedMaterialSign_replaceMaterial (segment : Segment) (outside : QueryImpl HashSpec Id)
    (material : Material) (replacement frontier root : Digest) (message : Message) :
    erasedMaterialSign segment outside (replaceMaterial segment material replacement) frontier root message =
      erasedMaterialSign segment outside material frontier root message := by
  simp only [erasedMaterialSign, replaceMaterial_twice]

/-- The actual counted prepared signer equals a view independent of its selected material
coordinate once the selected chain frontier is supplied. Private samples remain real samples. -/
theorem counted_prepared_sign_erased (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (material : Material) (root : Digest) (message : Message)
    (hparameter : parameter material = segment.parameter)
    (hcutoff : ReferenceCutoff segment (preparedOracle outside 0 (replaceMaterial segment material 0)) 0) :
    simulateQ (fixedPreparedWorld (answer segment tables high outside))
      (countPreparedQueries (PreparedScheme.sign material root message)) =
    erasedMaterialSign segment outside material
      (SphincsSecurity.Concrete.PartialChainEndpoint.evaluate tables
        (materialSecrets material (address segment))) root message := by
  have hcutoff' := ((prepared_replaceMaterial_agreement segment outside material 0 0).cutoff
    segment hparameter).1 hcutoff
  rw [counted_prepared_sign_from_referenceCutoff segment tables high outside material root message
    hparameter hcutoff']
  unfold erasedMaterialSign
  simp only [replaceMaterial_parameter]
  rw [publicSignWithCost_replaceMaterial segment outside material 0 _ _
    ⟨0, parameter material, root⟩ message hparameter rfl]
  have hsurrogates :
      (fun level => evalWithAnswerFn (preparedOracle outside 0 (replaceMaterial segment material 0))
        (Seeded.surrogate segment.parameter 0 level : OracleComp HashSpec Digest)) =
      (fun level => evalWithAnswerFn (preparedOracle outside 0 material)
        (Seeded.surrogate segment.parameter 0 level : OracleComp HashSpec Digest)) := by
    funext level
    rw [← hparameter]
    exact surrogate_replaceMaterial segment outside material 0 0 level
  rw [hsurrogates]

end LeanSphincs.Security.Prefix
