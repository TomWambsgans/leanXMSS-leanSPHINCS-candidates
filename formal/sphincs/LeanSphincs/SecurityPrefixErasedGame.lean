import LeanSphincs.SecurityPrefixErasedKeygen

/-! Composition of the erased honest view through the full adaptive adversarial interaction.
Ordinary hash requests keep their actual answers; the original hash cost and signing log are
preserved. This is the deterministic interface for a subsequent stopped-oracle coupling. -/

open OracleComp OracleSpec

namespace LeanSphincs.Security.Prefix
open Concrete Completeness SeedModel PreparedScheme MaterialGameCoupling
open SeedCoupling
open SphincsSecurity.QueryCap

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000
attribute [local irreducible] PreparedScheme.sign PreparedScheme.keygen
  Randomized.sign digestAttemptLimit encodingAttemptLimit erasedMaterialSign
  preparedOracle answer

noncomputable def fixedPreparedCost (f : QueryImpl HashSpec Id) :
    QueryImpl PreparedWorld (AddWriterT Nat PMF) :=
  (fixedPreparedWorld f).withAddCost (fun | .inl _ => 0 | .inr _ => 1)

noncomputable def fixedWorldCost (f : QueryImpl HashSpec Id) :
    QueryImpl OracleWorld (AddWriterT Nat PMF) :=
  (fixedHashWorld f).withAddCost (fun | .inl _ => 0 | .inr _ => 1)

theorem counted_fixedPreparedCost (f : QueryImpl HashSpec Id) {α : Type}
    (computation : OracleComp PreparedWorld α) :
    simulateQ (fixedPreparedWorld f) (countPreparedQueries computation) =
      (simulateQ (fixedPreparedCost f) computation).run := by
  rw [countPreparedQueries, simulate_withCost]
  congr 2
  funext input
  cases input <;> rfl

theorem fixedPreparedCost_ordinary (f : QueryImpl HashSpec Id) (input : OracleWorld.Domain) :
    simulateQ (fixedPreparedCost f) (ordinaryWorld input) = fixedWorldCost f input := by
  cases input <;> rw [ordinaryWorld, simulateQ_spec_query] <;> rfl

theorem map_logging_query {I J : Type} {spec : OracleSpec I} {target : OracleSpec J}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (outer : QueryImpl target m) (inner : QueryImpl spec (OracleComp target)) (input : I) :
    (outer.writerTMapBase inner.withLogging) input =
      (QueryImpl.withLogging (spec := spec) (fun t => simulateQ outer (inner t))) input := by
  apply WriterT.ext
  simp only [QueryImpl.writerTMapBase, QueryImpl.run_withLogging_apply]
  change simulateQ outer (inner input >>= fun output =>
    pure (output, (show QueryLog spec from [⟨input, output⟩]))) = _
  simp only [simulateQ_bind, simulateQ_pure]

theorem map_lift_query {I J : Type} {spec : OracleSpec I} {target : OracleSpec J}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {log : Type} [EmptyCollection log] [Append log]
    (outer : QueryImpl target m) (inner : QueryImpl spec (OracleComp target)) (input : I) :
    (outer.writerTMapBase (inner.liftTarget (WriterT log (OracleComp target)))) input =
      (liftM (simulateQ outer (inner input)) : WriterT log m (spec.Range input)) := by
  apply WriterT.ext
  change simulateQ outer ((fun output => (output, (∅ : log))) <$> inner input) = _
  rw [simulateQ_map]
  rfl

theorem fixedPreparedCost_ordinary_program (f : QueryImpl HashSpec Id) {α : Type}
    (computation : OracleComp OracleWorld α) :
    simulateQ (fixedPreparedCost f) (simulateQ ordinaryWorld computation) =
      simulateQ (fixedWorldCost f) computation := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext input
  exact fixedPreparedCost_ordinary f input

theorem fixedPreparedCost_lift_hash (f : QueryImpl HashSpec Id) {α : Type}
    (computation : OracleComp HashSpec α) :
    simulateQ (fixedPreparedCost f) (liftM computation : OracleComp PreparedWorld α) =
      simulateQ (fixedWorldCost f) (liftM computation : OracleComp OracleWorld α) := by
  rw [← ordinaryWorld_lift_hash, fixedPreparedCost_ordinary_program]

theorem countHashQueries_eq_sourceCount {α : Type} (computation : OracleComp OracleWorld α) :
    countHashQueries computation = counted SourceHash computation := by
  unfold countHashQueries
  congr 1
  funext input
  cases input <;> simp only [SourceHash, Bool.false_eq_true]

variable [Params]

noncomputable def erasedInteraction (segment : Segment) (outside raw : QueryImpl HashSpec Id)
    (material : Material) (frontier root : Digest) :
    QueryImpl (OracleWorld + SigningSpec)
      (WriterT (QueryLog SigningSpec) (AddWriterT Nat PMF)) :=
  (fixedWorldCost raw).liftTarget (WriterT (QueryLog SigningSpec) (AddWriterT Nat PMF)) +
    QueryImpl.withLogging (spec := SigningSpec)
    (m := AddWriterT Nat PMF)
    (fun message => (WriterT.mk (erasedMaterialSign segment outside material frontier root message) :
      AddWriterT Nat PMF (Option Signature)))

theorem fixedPreparedCost_sign_erased (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (material : Material) (root : Digest) (message : Message)
    (hparameter : parameter material = segment.parameter)
    (hcutoff : ReferenceCutoff segment (preparedOracle outside 0 (replaceMaterial segment material 0)) 0) :
    simulateQ (fixedPreparedCost (answer segment tables high outside))
      (PreparedScheme.sign material root message) =
    WriterT.mk (erasedMaterialSign segment outside material
      (SphincsSecurity.Concrete.PartialChainEndpoint.evaluate tables
        (materialSecrets material (address segment))) root message) := by
  apply WriterT.ext
  rw [← counted_fixedPreparedCost]
  exact counted_prepared_sign_erased segment tables high outside material root message hparameter hcutoff

theorem erasedInteraction_eq (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (material : Material) (root : Digest)
    (hparameter : parameter material = segment.parameter)
    (hcutoff : ReferenceCutoff segment (preparedOracle outside 0 (replaceMaterial segment material 0)) 0) :
    (fixedPreparedCost (answer segment tables high outside)).writerTMapBase
      (ordinaryWorld.liftTarget (WriterT (QueryLog SigningSpec) (OracleComp PreparedWorld)) +
        materialSigningOracle material root) =
    erasedInteraction segment outside (answer segment tables high outside) material
      (SphincsSecurity.Concrete.PartialChainEndpoint.evaluate tables
        (materialSecrets material (address segment))) root := by
  funext input
  cases input with
  | inl input =>
      change ((fixedPreparedCost (answer segment tables high outside)).writerTMapBase
        (ordinaryWorld.liftTarget (WriterT (QueryLog SigningSpec) (OracleComp PreparedWorld)))) input = _
      rw [map_lift_query, fixedPreparedCost_ordinary]
      rfl
  | inr message =>
      change ((fixedPreparedCost (answer segment tables high outside)).writerTMapBase
        (QueryImpl.withLogging (spec := SigningSpec)
          (fun message => PreparedScheme.sign material root message))) message = _
      rw [map_logging_query]
      have hsign : (fun message => simulateQ (fixedPreparedCost (answer segment tables high outside))
          (PreparedScheme.sign material root message)) =
        (fun message => WriterT.mk (erasedMaterialSign segment outside material
          (SphincsSecurity.Concrete.PartialChainEndpoint.evaluate tables
            (materialSecrets material (address segment))) root message)) := by
        funext message
        exact fixedPreparedCost_sign_erased segment tables high outside material root message hparameter hcutoff
      exact congrArg (fun impl : QueryImpl SigningSpec (AddWriterT Nat PMF) =>
        impl.withLogging message) hsign

theorem counted_adversary_erased (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (material : Material) (root : Digest) (adversary : Adversary)
    (hparameter : parameter material = segment.parameter)
    (hcutoff : ReferenceCutoff segment (preparedOracle outside 0 (replaceMaterial segment material 0)) 0) :
    simulateQ (fixedPreparedWorld (answer segment tables high outside))
      (countPreparedQueries
        (simulateQ (ordinaryWorld.liftTarget (WriterT (QueryLog SigningSpec) (OracleComp PreparedWorld)) +
          materialSigningOracle material root) (adversary.main ⟨root, parameter material⟩)).run) =
    (simulateQ (erasedInteraction segment outside (answer segment tables high outside) material
      (SphincsSecurity.Concrete.PartialChainEndpoint.evaluate tables
        (materialSecrets material (address segment))) root)
      (adversary.main ⟨root, parameter material⟩)).run.run := by
  rw [counted_fixedPreparedCost, QueryImpl.simulateQ_writerTMapBase_run,
    erasedInteraction_eq segment tables high outside material root hparameter hcutoff]

/-- With the frontier supplied, replacing the selected low secret does not change any honest
query handler, even when calls are chosen adaptively from the complete preceding transcript. -/
theorem erasedInteraction_replaceMaterial (segment : Segment) (outside raw : QueryImpl HashSpec Id)
    (material : Material) (replacement frontier root : Digest) :
    erasedInteraction segment outside raw (replaceMaterial segment material replacement) frontier root =
      erasedInteraction segment outside raw material frontier root := by
  have hsign : erasedMaterialSign segment outside (replaceMaterial segment material replacement)
      frontier root = erasedMaterialSign segment outside material frontier root := by
    funext message
    exact erasedMaterialSign_replaceMaterial segment outside material replacement frontier root message
  exact congrArg (fun signLaw : Message → PMF (Option Signature × Nat) =>
    (fixedWorldCost raw).liftTarget (WriterT (QueryLog SigningSpec) (AddWriterT Nat PMF)) +
      QueryImpl.withLogging (spec := SigningSpec) (m := AddWriterT Nat PMF)
        (fun message => WriterT.mk (signLaw message))) hsign

theorem erased_adversary_replaceMaterial (segment : Segment) (outside raw : QueryImpl HashSpec Id)
    (material : Material) (replacement frontier root : Digest) (adversary : Adversary) :
    (simulateQ (erasedInteraction segment outside raw (replaceMaterial segment material replacement)
      frontier root) (adversary.main ⟨root, parameter (replaceMaterial segment material replacement)⟩)).run.run =
    (simulateQ (erasedInteraction segment outside raw material frontier root)
      (adversary.main ⟨root, parameter material⟩)).run.run := by
  rw [erasedInteraction_replaceMaterial, replaceMaterial_parameter]

noncomputable def erasedRest (segment : Segment) (outside raw : QueryImpl HashSpec Id)
    (material : Material) (frontier root : Digest) (adversary : Adversary) : AddWriterT Nat PMF Bool := do
  let pk : PublicKey := ⟨root, parameter material⟩
  let (forgery, log) ← (simulateQ (erasedInteraction segment outside raw material frontier root)
    (adversary.main pk)).run
  let verified ← simulateQ (fixedWorldCost raw)
    (liftM (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool) :
      OracleComp OracleWorld Bool)
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

theorem fixedPreparedCost_rest_erased (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (material : Material) (root : Digest) (adversary : Adversary)
    (hparameter : parameter material = segment.parameter)
    (hcutoff : ReferenceCutoff segment (preparedOracle outside 0 (replaceMaterial segment material 0)) 0) :
    simulateQ (fixedPreparedCost (answer segment tables high outside))
      (targetRest material adversary ⟨root, parameter material⟩) =
    erasedRest segment outside (answer segment tables high outside) material
      (SphincsSecurity.Concrete.PartialChainEndpoint.evaluate tables
        (materialSecrets material (address segment))) root adversary := by
  simp only [targetRest, simulateQ_bind, simulateQ_pure,
    QueryImpl.simulateQ_writerTMapBase_run,
    erasedInteraction_eq segment tables high outside material root hparameter hcutoff,
    fixedPreparedCost_lift_hash, erasedRest]

theorem erasedRest_replaceMaterial (segment : Segment) (outside raw : QueryImpl HashSpec Id)
    (material : Material) (replacement frontier root : Digest) (adversary : Adversary) :
    erasedRest segment outside raw (replaceMaterial segment material replacement) frontier root adversary =
      erasedRest segment outside raw material frontier root adversary := by
  simp only [erasedRest, erasedInteraction_replaceMaterial, replaceMaterial_parameter]

theorem fixedPreparedCost_keygen_erased (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (material : Material)
    (hparameter : parameter material = segment.parameter) :
    simulateQ (fixedPreparedCost (answer segment tables high outside))
      (liftM (PreparedScheme.keygen material) : OracleComp PreparedWorld (PublicKey × Seeded.SecretKey)) =
    WriterT.mk (PMF.pure
      (let root := erasedMaterialRoot segment outside material
        (SphincsSecurity.Concrete.PartialChainEndpoint.evaluate tables
          (materialSecrets material (address segment)))
       ((⟨root, parameter material⟩, ⟨0, parameter material, root⟩),
         Multiplicative.ofAdd (258 * 2 ^ subtreeHeight + 2 * (totalHeight - subtreeHeight))))) := by
  apply WriterT.ext
  rw [← counted_fixedPreparedCost]
  rw [PreparedScheme.keygen, ← compileWorld_lift_hash, countPrepared_compileWorld,
    fixedPreparedWorld_compileWorld, countHashQueries_eq_sourceCount,
    fixedHashWorld_counted_lift_hash, hashCalls_keygenFromSeed]
  have hkey := prepared_keygen_erased segment tables high outside material hparameter
  rw [PreparedScheme.keygen, eval_compiledHash] at hkey
  rw [hkey]
  rfl

noncomputable def erasedGame (segment : Segment) (outside raw : QueryImpl HashSpec Id)
    (material : Material) (frontier : Digest) (adversary : Adversary) : PMF (Bool × Nat) :=
  let root := erasedMaterialRoot segment outside material frontier
  (fun result => (result.1,
    (258 * 2 ^ subtreeHeight + 2 * (totalHeight - subtreeHeight)) + result.2)) <$>
    (erasedRest segment outside raw material frontier root adversary).run

/-- The whole material game factors through a supplied frontier, including key generation,
adaptive private-randomized signing, verification, strong freshness and the original cost. -/
theorem counted_materialGame_erased (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (material : Material) (adversary : Adversary)
    (hparameter : parameter material = segment.parameter)
    (hcutoff : ReferenceCutoff segment (preparedOracle outside 0 (replaceMaterial segment material 0)) 0) :
    simulateQ (fixedPreparedWorld (answer segment tables high outside))
      (countPreparedQueries (materialGame material adversary)) =
    erasedGame segment outside (answer segment tables high outside) material
      (SphincsSecurity.Concrete.PartialChainEndpoint.evaluate tables
        (materialSecrets material (address segment))) adversary := by
  rw [counted_fixedPreparedCost, materialGame_eq_bind, simulateQ_bind,
    fixedPreparedCost_keygen_erased segment tables high outside material hparameter]
  simp only [WriterT.run_bind, WriterT.run_mk, ← PMF.monad_pure_eq_pure, pure_bind]
  rw [fixedPreparedCost_rest_erased segment tables high outside material _ adversary hparameter hcutoff]
  rfl

theorem erasedGame_replaceMaterial (segment : Segment) (outside raw : QueryImpl HashSpec Id)
    (material : Material) (replacement frontier : Digest) (adversary : Adversary) :
    erasedGame segment outside raw (replaceMaterial segment material replacement) frontier adversary =
      erasedGame segment outside raw material frontier adversary := by
  simp only [erasedGame, erasedMaterialRoot_replaceMaterial, erasedRest_replaceMaterial]

end LeanSphincs.Security.Prefix
