import LeanSphincs.SecurityPrefixCostTransfer
import LeanSphincs.SecurityMaterialGameCoupling

/-! Fixed-function interpretation of the prepared material compiler, followed by the exact
frontier factoring of honest signing. Virtual derivation ticks retain their original cost. -/

open OracleComp OracleSpec

namespace LeanSphincs.Security.Prefix
open Concrete SeedModel PreparedScheme SeedCoupling

set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] programCache digestAttemptLimit encodingAttemptLimit
  Randomized.sign Randomized.finishSign

def fixedPreparedHash (outside : QueryImpl HashSpec Id) : QueryImpl PreparedHashSpec Id
  | .inl input => outside input
  | .inr _ => ()

noncomputable def fixedPreparedWorld (outside : QueryImpl HashSpec Id) : QueryImpl PreparedWorld PMF :=
  (fun input => PMF.uniformOfFintype (unifSpec.Range input) : QueryImpl unifSpec PMF) +
    (fixedPreparedHash outside).liftTarget PMF

theorem eval_compileHash (outside : QueryImpl HashSpec Id) (seed : MasterSeed)
    (material : Material) (input : HashInput) :
    evalWithAnswerFn (fixedPreparedHash outside) (compileHash seed material input) =
      preparedOracle outside seed material input := by
  unfold compileHash preparedOracle
  cases hentry : programCache ∅ seed material input with
  | none => rfl
  | some output => rfl

theorem fixedPreparedWorld_lift_hash (outside : QueryImpl HashSpec Id) {α : Type}
    (computation : OracleComp PreparedHashSpec α) :
    simulateQ (fixedPreparedWorld outside) (liftM computation : OracleComp PreparedWorld α) =
      PMF.pure (evalWithAnswerFn (fixedPreparedHash outside) computation) := by
  rw [fixedPreparedWorld, QueryImpl.simulateQ_add_liftM_right, simulateQ_liftTarget]
  rfl

theorem fixedPreparedWorld_compileWorld_query (outside : QueryImpl HashSpec Id)
    (seed : MasterSeed) (material : Material) (input : OracleWorld.Domain) :
    simulateQ (fixedPreparedWorld outside) (compileWorld seed material input) =
      fixedHashWorld (preparedOracle outside seed material) input := by
  cases input with
  | inl sample =>
      change simulateQ (fixedPreparedWorld outside) (liftM (PreparedWorld.query (.inl sample))) = _
      rw [simulateQ_spec_query]
      rfl
  | inr input =>
      change simulateQ (fixedPreparedWorld outside) (liftM (compileHash seed material input)) = _
      rw [fixedPreparedWorld_lift_hash, eval_compileHash]
      rfl

/-- Honest prepared computations have exactly the fixed hash law of the programmed material
oracle. This statement retains private random sampling and applies to cost-instrumented code. -/
theorem fixedPreparedWorld_compileWorld (outside : QueryImpl HashSpec Id)
    (seed : MasterSeed) (material : Material) {α : Type} (computation : OracleComp OracleWorld α) :
    simulateQ (fixedPreparedWorld outside) (simulateQ (compileWorld seed material) computation) =
    simulateQ (fixedHashWorld (preparedOracle outside seed material)) computation := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext input
  exact fixedPreparedWorld_compileWorld_query outside seed material input

theorem preparedOracle_answer (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (seed : MasterSeed) (material : Material) :
    preparedOracle (answer segment tables high outside) seed material =
      answer segment tables high (preparedOracle outside seed material) := by
  funext bytes
  cases hparse : parse segment bytes with
  | none => simp only [preparedOracle, answer, hparse]
  | some query =>
      have hbytes := (parse_some_iff segment bytes query).mp hparse
      rw [hbytes, show preparedOracle (answer segment tables high outside) seed material (input segment query) =
        answer segment tables high outside (input segment query) from preparedOracle_verifier _ _ _ _ _ _]
      simp only [answer, parse_input]

def materialSecrets (material : Material) : Secrets :=
  fun chain => truncateHash (material.2 (.inl chain))

theorem derivedSecrets_prepared (outside : QueryImpl HashSpec Id) (seed : MasterSeed)
    (material : Material) :
    derivedSecrets (preparedOracle outside seed material) (parameter material) seed =
      materialSecrets material := by
  funext chain
  rcases chain with ⟨lay, tree, leaf, index⟩
  exact eval_secret_prepared _ seed material (preparedOracle_agreement outside seed material)
    (.inl (lay, tree, leaf, index))

variable [Params]

theorem counted_prepared_sign (outside : QueryImpl HashSpec Id) (material : Material)
    (root : Digest) (message : Message) :
    simulateQ (fixedPreparedWorld outside) (countPreparedQueries (PreparedScheme.sign material root message)) =
    simulateQ (fixedHashWorld (preparedOracle outside 0 material))
      (SphincsSecurity.QueryCap.counted SourceHash (Randomized.sign ⟨0, parameter material, root⟩ message)) := by
  classical
  rw [PreparedScheme.sign, countPrepared_compileWorld, fixedPreparedWorld_compileWorld]
  unfold countHashQueries
  have hpred : (fun query : OracleWorld.Domain => (show Prop from query matches .inr _)) = SourceHash := by
    funext input
    apply propext
    cases input <;> simp [SourceHash]
  congr 1
  have hcongr (left right : OracleWorld.Domain → Prop) (h : left = right)
      (dl : DecidablePred left) (dr : DecidablePred right) :
      @SphincsSecurity.QueryCap.counted _ OracleWorld _ left dl
        (Randomized.sign ⟨0, parameter material, root⟩ message) =
      @SphincsSecurity.QueryCap.counted _ OracleWorld _ right dr
        (Randomized.sign ⟨0, parameter material, root⟩ message) := by
    subst right
    cases Subsingleton.elim dl dr
    rfl
  exact hcongr _ _ hpred _ _

/-- Prepared signing exposes the selected chain through its frontier alone, while its original
hash count is retained. The outside prepared table is still explicit at this stage. -/
theorem counted_prepared_sign_from_referenceCutoff (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (material : Material) (root : Digest) (message : Message)
    (hparameter : parameter material = segment.parameter)
    (hcutoff : ReferenceCutoff segment (preparedOracle outside 0 material) 0) :
    simulateQ (fixedPreparedWorld (answer segment tables high outside))
      (countPreparedQueries (PreparedScheme.sign material root message)) =
    publicSignWithCost segment (preparedOracle outside 0 material) (materialSecrets material)
      (SphincsSecurity.Concrete.PartialChainEndpoint.evaluate tables
        (materialSecrets material (address segment)))
      (fun level => evalWithAnswerFn (preparedOracle outside 0 material)
        (Seeded.surrogate segment.parameter 0 level : OracleComp HashSpec Digest))
      ⟨0, parameter material, root⟩ message := by
  rw [counted_prepared_sign, preparedOracle_answer,
    counted_sign_from_referenceCutoff segment tables high (preparedOracle outside 0 material)
      ⟨0, parameter material, root⟩ message hparameter hcutoff]
  rw [← hparameter, derivedSecrets_prepared]

end LeanSphincs.Security.Prefix
