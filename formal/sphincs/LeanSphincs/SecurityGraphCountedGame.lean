import LeanSphincs.SecurityGraphCountedSigner

/-! The counted graph signer composes through an arbitrary adaptive adversary and the
actual verifier. The resulting explicit-reveal program retains the strong signing log. -/

open OracleComp OracleSpec
namespace LeanSphincs.Security.GraphView
open Concrete Completeness Prefix HiddenGraph SeedCoupling
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] signCostSource Randomized.sign Seeded.keygenFromSeed

def ordinaryCostSource : QueryImpl OracleWorld (OracleComp CostSpec)
  | .inl request => liftM (CostSpec.query (.inl (.inl request)))
  | .inr request => liftM (CostSpec.query (.inl (.inr (.inl request))))

theorem fixedCostSource_ordinary (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table)
    (request : OracleWorld.Domain) :
    simulateQ (fixedCostSource f table) (ordinaryCostSource request) = fixedWorldCost f request := by
  cases request <;> rw [ordinaryCostSource, simulateQ_spec_query] <;> rfl

variable [Params]

noncomputable def costInteraction (parameter : PublicParameter) (data : PublicData) :
    QueryImpl (OracleWorld + SigningSpec) (WriterT (QueryLog SigningSpec) (OracleComp CostSpec)) :=
  ordinaryCostSource.liftTarget (WriterT (QueryLog SigningSpec) (OracleComp CostSpec)) +
    QueryImpl.withLogging (spec := SigningSpec) (m := OracleComp CostSpec)
      (fun message => signCostSource parameter data message)

theorem fixedCostSource_interaction (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (table : HiddenGraph.Table)
    (hdata : DataCorrect f parameter seed data) (htable : CoordinatesCorrect f parameter seed table) :
    (fixedCostSource f table).writerTMapBase (costInteraction parameter data) =
      (fixedWorldCost f).writerTMapBase
        (QueryImpl.ofLift OracleWorld
          (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
          signingOracle ⟨seed, parameter, data.root⟩) := by
  funext request
  cases request with
  | inl request =>
      change ((fixedCostSource f table).writerTMapBase
        (ordinaryCostSource.liftTarget (WriterT (QueryLog SigningSpec) (OracleComp CostSpec)))) request = _
      rw [map_lift_query, fixedCostSource_ordinary]
      apply WriterT.ext
      change (fun value => (value, (∅ : QueryLog SigningSpec))) <$> fixedWorldCost f request =
        simulateQ (fixedWorldCost f) ((fun value => (value, (∅ : QueryLog SigningSpec))) <$>
          (liftM (OracleWorld.query request) : OracleComp OracleWorld _))
      rw [simulateQ_map, simulateQ_spec_query]
  | inr message =>
      change ((fixedCostSource f table).writerTMapBase
        (QueryImpl.withLogging (spec := SigningSpec) (m := OracleComp CostSpec)
          (fun message => signCostSource parameter data message))) message =
        ((fixedWorldCost f).writerTMapBase (signingOracle ⟨seed, parameter, data.root⟩)) message
      rw [signingOracle, map_logging_query, map_logging_query]
      have hsign : (fun message => simulateQ (fixedCostSource f table)
          (signCostSource parameter data message)) =
          (fun message => simulateQ (fixedWorldCost f)
            (Randomized.sign ⟨seed, parameter, data.root⟩ message)) := by
        funext message
        exact signCostSource_correct f parameter seed data table hdata htable message
      exact congrArg (fun impl : QueryImpl SigningSpec (AddWriterT Nat PMF) =>
        impl.withLogging message) hsign

noncomputable def costRest (parameter : PublicParameter) (data : PublicData) (adversary : Adversary) :
    OracleComp CostSpec Bool := do
  let pk : PublicKey := ⟨data.root, parameter⟩
  let (forgery, log) ← (simulateQ (costInteraction parameter data) (adversary.main pk)).run
  let verified ← liftM (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool)
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

theorem fixedCostSource_rest (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (table : HiddenGraph.Table)
    (hdata : DataCorrect f parameter seed data) (htable : CoordinatesCorrect f parameter seed table)
    (adversary : Adversary) :
    simulateQ (fixedCostSource f table) (costRest parameter data adversary) =
      simulateQ (fixedWorldCost f) (do
        let pk : PublicKey := ⟨data.root, parameter⟩
        let (forgery, log) ← (simulateQ (QueryImpl.ofLift OracleWorld
          (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
          signingOracle ⟨seed, parameter, data.root⟩) (adversary.main pk)).run
        let verified ← liftM (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool)
        return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified) := by
  simp only [costRest, simulateQ_bind, simulateQ_pure, QueryImpl.simulateQ_writerTMapBase_run,
    fixedCostSource_interaction f parameter seed data table hdata htable, fixedCostSource_lift_hash]

noncomputable def costGame (parameter : PublicParameter) (data : PublicData) (adversary : Adversary) :
    OracleComp CostSpec Bool := do
  HiddenCost.tick (258 * 2 ^ subtreeHeight + 2 * (totalHeight - subtreeHeight))
  costRest parameter data adversary

theorem fixedWorldCost_keygen_graph (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (hdata : DataCorrect f parameter seed data)
    (hparameter : evalWithAnswerFn f (deriveKey 0 .parameter seed : OracleComp HashSpec Digest) = parameter) :
    simulateQ (fixedWorldCost f) (liftM (Seeded.keygenFromSeed seed) :
      OracleComp OracleWorld (PublicKey × Seeded.SecretKey)) =
      WriterT.mk (PMF.pure ((⟨data.root, parameter⟩, ⟨seed, parameter, data.root⟩),
        Multiplicative.ofAdd (258 * 2 ^ subtreeHeight + 2 * (totalHeight - subtreeHeight)))) := by
  rw [fixedWorldCost_lift_hash, hashCalls_keygenFromSeed]
  simp only [Seeded.keygenFromSeed, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    hparameter, ← hdata.root]

/-- Fixed-oracle equality for the complete actual game, with its original hash budget.
The graph data and coordinates must come from a consistent preparation of that oracle. -/
theorem costGame_correct (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (table : HiddenGraph.Table)
    (hdata : DataCorrect f parameter seed data) (htable : CoordinatesCorrect f parameter seed table)
    (hparameter : evalWithAnswerFn f (deriveKey 0 .parameter seed : OracleComp HashSpec Digest) = parameter)
    (adversary : Adversary) :
    simulateQ (fixedCostSource f table) (costGame parameter data adversary) =
      simulateQ (fixedWorldCost f) (gameAfterSeed adversary seed) := by
  simp only [costGame, gameAfterSeed, simulateQ_bind, fixedCostSource_tick]
  rw [fixedWorldCost_keygen_graph f parameter seed data hdata hparameter]
  apply WriterT.ext
  simp only [WriterT.run_bind, WriterT.run_mk, AddWriterT.run_addTell,
    ← PMF.monad_pure_eq_pure, pure_bind]
  rw [fixedCostSource_rest f parameter seed data table hdata htable]
  simp only [simulateQ_bind, WriterT.run_bind]

end LeanSphincs.Security.GraphView
