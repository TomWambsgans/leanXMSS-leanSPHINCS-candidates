import LeanSphincs.SecurityPrefixMaterialCost

/-! Public key generation, including its original total hash cost, depends on a selected
chain's hidden material coordinate only through the supplied chain frontier. -/

open OracleComp OracleSpec

namespace LeanSphincs.Security.Prefix
open Concrete Completeness SeedModel PreparedScheme

attribute [local irreducible] Seeded.treeNode Seeded.spineNode Seeded.treeRoot
  programCache preparedOracle
set_option backward.isDefEq.respectTransparency false

theorem eval_compiledHash {α : Type} (outside : QueryImpl HashSpec Id) (seed : MasterSeed)
    (material : Material) (computation : OracleComp HashSpec α) :
    evalWithAnswerFn (fixedPreparedHash outside) (simulateQ (compileHash seed material) computation) =
      evalWithAnswerFn (preparedOracle outside seed material) computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, evalWithAnswerFn_pure]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, evalWithAnswerFn_bind, eval_compileHash,
        show evalWithAnswerFn (preparedOracle outside seed material) (liftM (HashSpec.query input)) =
          preparedOracle outside seed material input from simulateQ_spec_query _ input, ih]

variable [Params]

theorem hashCalls_spineNode (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (seed : MasterSeed) (steps : Nat)
    (hsteps : steps ≤ totalHeight - subtreeHeight) :
    hashCalls f (Seeded.spineNode parameter lay tree seed steps : OracleComp HashSpec Digest) =
      (258 * 2 ^ subtreeHeight - 1) + 2 * steps := by
  induction steps with
  | zero => simp only [Seeded.spineNode, hashCalls_treeNode, Nat.mul_zero, Nat.add_zero]
  | succ steps ih =>
      have hlevel : subtreeHeight + steps < totalHeight := by omega
      rw [Seeded.spineNode, hashCalls_bind, ih (by omega), hashCalls_bind]
      simp only [Seeded.surrogate, dif_pos hlevel, hashCalls_deriveKey]
      split <;> rw [hashCalls_tweakableHash] <;> omega

theorem hashCalls_keygenFromSeed (f : QueryImpl HashSpec Id) (seed : MasterSeed) :
    hashCalls f (Seeded.keygenFromSeed seed) =
      258 * 2 ^ subtreeHeight + 2 * (totalHeight - subtreeHeight) := by
  simp only [Seeded.keygenFromSeed, hashCalls_bind, hashCalls_deriveKey, Seeded.treeRoot,
    hashCalls_spineNode f _ _ _ seed _ (le_refl _), hashCalls_pure, Nat.add_zero]
  have := Nat.two_pow_pos subtreeHeight
  omega

theorem publicSpine_replaceMaterial (segment : Segment) (outside : QueryImpl HashSpec Id)
    (material : Material) (replacement frontier : Digest) (surrogates : Nat → Digest)
    (seed : MasterSeed) (lay : Layer) (tree : TreeIndex) (steps : Nat)
    (hparameter : parameter material = segment.parameter) :
    publicSpine segment (preparedOracle outside seed (replaceMaterial segment material replacement))
      (materialSecrets (replaceMaterial segment material replacement)) frontier surrogates lay tree steps =
    publicSpine segment (preparedOracle outside seed material) (materialSecrets material)
      frontier surrogates lay tree steps := by
  rw [materialSecrets_replaceMaterial, publicSpine_replaceSecret]
  exact (prepared_replaceMaterial_agreement segment outside material replacement seed).spine
    segment hparameter _ _ _ _ _ _

noncomputable def erasedMaterialRoot (segment : Segment) (outside : QueryImpl HashSpec Id)
    (material : Material) (frontier : Digest) : Digest :=
  let erased := replaceMaterial segment material 0
  publicSpine segment (preparedOracle outside 0 erased) (materialSecrets erased) frontier
    (fun level => evalWithAnswerFn (preparedOracle outside 0 erased)
      (Seeded.surrogate segment.parameter 0 level : OracleComp HashSpec Digest))
    topLayer rootTree (totalHeight - subtreeHeight)

theorem erasedMaterialRoot_replaceMaterial (segment : Segment) (outside : QueryImpl HashSpec Id)
    (material : Material) (replacement frontier : Digest) :
    erasedMaterialRoot segment outside (replaceMaterial segment material replacement) frontier =
      erasedMaterialRoot segment outside material frontier := by
  simp only [erasedMaterialRoot, replaceMaterial_twice]

theorem prepared_root_erased (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (material : Material)
    (hparameter : parameter material = segment.parameter) :
    evalWithAnswerFn (preparedOracle (answer segment tables high outside) 0 material)
      (Seeded.treeRoot (parameter material) topLayer rootTree 0 : OracleComp HashSpec Digest) =
    erasedMaterialRoot segment outside material
      (SphincsSecurity.Concrete.PartialChainEndpoint.evaluate tables
        (materialSecrets material (address segment))) := by
  rw [hparameter, preparedOracle_answer, treeRoot_from_frontier]
  rw [← hparameter, derivedSecrets_prepared]
  unfold erasedMaterialRoot
  rw [publicSpine_replaceMaterial segment outside material 0 _ _ 0 topLayer rootTree _ hparameter]
  have hsurrogates :
      (fun level => evalWithAnswerFn (preparedOracle outside 0 (replaceMaterial segment material 0))
        (Seeded.surrogate segment.parameter 0 level : OracleComp HashSpec Digest)) =
      (fun level => evalWithAnswerFn (preparedOracle outside 0 material)
        (Seeded.surrogate segment.parameter 0 level : OracleComp HashSpec Digest)) := by
    funext level
    rw [← hparameter]
    exact surrogate_replaceMaterial segment outside material 0 0 level
  rw [hsurrogates, hparameter]

/-- The actual material keygen result has an explicitly erased selected coordinate. -/
theorem prepared_keygen_erased (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (material : Material)
    (hparameter : parameter material = segment.parameter) :
    evalWithAnswerFn (fixedPreparedHash (answer segment tables high outside)) (PreparedScheme.keygen material) =
      let root := erasedMaterialRoot segment outside material
        (SphincsSecurity.Concrete.PartialChainEndpoint.evaluate tables
          (materialSecrets material (address segment)))
      (⟨root, parameter material⟩, ⟨0, parameter material, root⟩) := by
  rw [PreparedScheme.keygen, eval_compiledHash]
  simp only [Seeded.keygenFromSeed, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rw [eval_parameter_prepared _ 0 material
    (preparedOracle_agreement (answer segment tables high outside) 0 material)]
  rw [prepared_root_erased segment tables high outside material hparameter]

end LeanSphincs.Security.Prefix
