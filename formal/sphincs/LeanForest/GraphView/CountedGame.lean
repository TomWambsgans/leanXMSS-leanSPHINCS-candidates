import LeanForest.GraphView.Cost
import LeanForest.GraphView.HashCalls
import LeanForest.Scheme.LandedDigest

section

/-! The counted graph-reveal signer: its hash calls are honest queries, free and answered by the
same oracle, so on a fixed answer function it evaluates to the actual signature at no cost. -/

open OracleComp OracleSpec

namespace LeanForest.Security.GraphView

variable [Params]
open Concrete Completeness Prefix HiddenGraph
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] firstEncoding ReferenceChoice.search encodingAttemptLimit
  Seeded.finishSign digestAttemptLimit sequenceFin

abbrev CostSpec := HiddenCost.SourceCostSpec HashInput HashOutput Coordinate

noncomputable def fixedCostSource (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table) :
    QueryImpl CostSpec (AddWriterT Nat PMF) :=
  QueryImpl.withAddCost (spec := CostSpec)
    (fun | .inl request => fixedSource f table request | .inr query => PMF.pure (f query.input))
    HiddenCost.sourceCost

/-- An honest computation: each of its hash calls is an honest query. -/
noncomputable def honestly {α : Type} (computation : OracleComp HashSpec α) : OracleComp CostSpec α :=
  simulateQ (fun input => HiddenCost.honest (D := HashInput) (R := HashOutput) (ι := Coordinate) input)
    computation

theorem honestly_pure {α : Type} (value : α) : honestly (pure value : OracleComp HashSpec α) = pure value :=
  simulateQ_pure _ _

theorem honestly_bind {α β : Type} (computation : OracleComp HashSpec α)
    (next : α → OracleComp HashSpec β) :
    honestly (computation >>= next) = honestly computation >>= fun value => honestly (next value) :=
  simulateQ_bind _ _ _

theorem fixedCostSource_lift_hash (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table)
    {α : Type} (computation : OracleComp HashSpec α) :
    simulateQ (fixedCostSource f table) (liftM computation : OracleComp CostSpec α) =
      simulateQ (fixedWorldCost f) (liftM computation : OracleComp OracleWorld α) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [liftM_pure, simulateQ_pure]
  | query_bind input next ih =>
      simp only [liftM_bind, simulateQ_bind, ih]
      rfl

theorem fixedWorldCost_lift_hash (f : QueryImpl HashSpec Id)
    {α : Type} (computation : OracleComp HashSpec α) :
    simulateQ (fixedWorldCost f) (liftM computation : OracleComp OracleWorld α) =
      WriterT.mk (PMF.pure (evalWithAnswerFn f computation,
        Multiplicative.ofAdd (hashCalls f computation))) := by
  apply WriterT.ext
  have hcount : (simulateQ (fixedWorldCost f)
      (liftM computation : OracleComp OracleWorld α)).run =
      simulateQ (fixedHashWorld f) (QueryCap.counted SourceHash
        (liftM computation : OracleComp OracleWorld α)) := by
    rw [QueryCap.simulate_withCost]
    congr 2
    funext input
    cases input <;> rfl
  rw [hcount, fixedHashWorld_counted_lift_hash]
  rfl

theorem fixedCostSource_reveal (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table)
    (coordinate : Coordinate) :
    simulateQ (fixedCostSource f table)
      (HiddenCost.reveal (D := HashInput) (R := HashOutput) coordinate) =
      pure (table coordinate) := by
  rw [HiddenCost.reveal, simulateQ_spec_query]
  apply WriterT.ext
  simp [fixedCostSource, QueryImpl.withAddCost, QueryImpl.withCost,
    HiddenCost.sourceCost, fixedSource, fixedView]
  change (fun a => (a, (1 : Multiplicative Nat))) <$> PMF.pure (table coordinate) = _
  simp only [← PMF.monad_pure_eq_pure, map_pure]

theorem fixedCostSource_honest (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table)
    (input : HashInput) :
    simulateQ (fixedCostSource f table)
      (HiddenCost.honest (D := HashInput) (R := HashOutput) (ι := Coordinate) input) = pure (f input) := by
  rw [HiddenCost.honest, simulateQ_spec_query]
  apply WriterT.ext
  simp [fixedCostSource, QueryImpl.withAddCost, QueryImpl.withCost, HiddenCost.sourceCost]
  change (fun a => (a, (1 : Multiplicative Nat))) <$> PMF.pure (f input) = _
  simp only [← PMF.monad_pure_eq_pure, map_pure]

/-- An honest computation evaluates on the fixed answer function, at no cost. -/
theorem fixedCostSource_honestly (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table)
    {α : Type} (computation : OracleComp HashSpec α) :
    simulateQ (fixedCostSource f table) (honestly computation) = pure (evalWithAnswerFn f computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => rw [honestly_pure, simulateQ_pure, evalWithAnswerFn_pure]
  | query_bind input next ih =>
      rw [honestly_bind, simulateQ_bind, evalWithAnswerFn_bind]
      have hq : honestly (liftM (HashSpec.query input) : OracleComp HashSpec _) =
          HiddenCost.honest (D := HashInput) (R := HashOutput) (ι := Coordinate) input := by
        simp [honestly, HiddenCost.honest]
      rw [hq, fixedCostSource_honest, pure_bind, ih]
      rfl

theorem fixedCostSource_sequence_reveal (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table)
    {n : Nat} (which : Fin n → Coordinate) :
    simulateQ (fixedCostSource f table) (sequenceFin fun index =>
      HiddenCost.reveal (D := HashInput) (R := HashOutput) (which index)) =
      pure (fun index => table (which index)) := by
  induction n with
  | zero =>
      simp only [sequenceFin, simulateQ_pure]
      congr 1
      funext index
      exact index.elim0
  | succ n ih =>
      simp only [sequenceFin, simulateQ_bind, fixedCostSource_reveal, pure_bind,
        simulateQ_pure, ih]
      congr 1
      funext index
      cases index using Fin.cases <;> rfl

theorem fixedCostSource_sequenceFin_pure (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table)
    {α : Type} {n : Nat} (computation : Fin n → OracleComp CostSpec α) (values : Fin n → α)
    (h : ∀ i, simulateQ (fixedCostSource f table) (computation i) = pure (values i)) :
    simulateQ (fixedCostSource f table) (sequenceFin computation) = pure values := by
  induction n with
  | zero =>
      simp only [sequenceFin, simulateQ_pure]
      congr 1
      funext index
      exact index.elim0
  | succ n ih =>
      simp only [sequenceFin, simulateQ_bind, h 0, pure_bind, simulateQ_pure,
        ih (fun index => computation index.succ) (fun index => values index.succ) (fun i => h i.succ)]
      congr 1
      funext index
      cases index using Fin.cases <;> rfl

/-- The cost-level reveal of one opened forest chain, at and above its opened position. -/
noncomputable def revealChainCost (index : Index) (c : Coord) (mark : CoordMark) (j : SubIdx) (i : FChain) :
    OracleComp CostSpec (FPos → Digest) :=
  sequenceFin fun k : FPos =>
    if (openedPos mark j i).val ≤ k.val then
      HiddenCost.reveal (D := HashInput) (R := HashOutput) (.fchain index c mark.super j (mark.child j) i k)
    else pure 0

/-- One tree's opening at the cost level. -/
noncomputable def coordCostSource (data : PublicData) (index : Index) (c : Coord) (mark : CoordMark) :
    OracleComp CostSpec CoordOpening := do
  let sub ← sequenceFin fun j => do
    let cols ← sequenceFin fun i => revealChainCost index c mark j i
    return (⟨fun i => cols i (openedPos mark j i),
      data.subPath index c mark.super j (mark.child j)⟩ : SubOpening)
  return ⟨sub, data.topPath index c mark.super⟩

theorem fixed_forestCostSource (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table) (data : PublicData)
    (index : Index) (marks : Coord → CoordMark) :
    simulateQ (fixedCostSource f table) (sequenceFin fun c => coordCostSource data index c (marks c)) =
      pure (assembledForest data table index marks) := by
  apply fixedCostSource_sequenceFin_pure
  intro c
  have hcols : ∀ (j : SubIdx) (i : FChain), simulateQ (fixedCostSource f table) (revealChainCost index c (marks c) j i) =
      pure (fun k : FPos => if (openedPos (marks c) j i).val ≤ k.val then
        table (.fchain index c (marks c).super j ((marks c).child j) i k) else 0) := by
    intro j i
    apply fixedCostSource_sequenceFin_pure
    intro k
    split
    · exact fixedCostSource_reveal f table _
    · exact simulateQ_pure _ _
  have hsub : ∀ j : SubIdx, simulateQ (fixedCostSource f table) (do
      let cols ← sequenceFin fun i => revealChainCost index c (marks c) j i
      return (⟨fun i => cols i (openedPos (marks c) j i),
        data.subPath index c (marks c).super j ((marks c).child j)⟩ : SubOpening)) =
      pure (⟨fun i => table (.fchain index c (marks c).super j ((marks c).child j) i (openedPos (marks c) j i)),
        data.subPath index c (marks c).super j ((marks c).child j)⟩ : SubOpening) := by
    intro j
    rw [simulateQ_bind, fixedCostSource_sequenceFin_pure f table _ _ (hcols j), pure_bind, simulateQ_pure]
    simp only [le_refl, ↓reduceIte]
  rw [coordCostSource, simulateQ_bind, fixedCostSource_sequenceFin_pure f table _ _ hsub, pure_bind,
    simulateQ_pure]
  rfl


/-- The counter search of one layer at the cost level, by honest queries. -/
noncomputable def layerCostSearch (parameter : PublicParameter) (data : PublicData) (index : Index)
    (lay : Layer) : OracleComp CostSpec (Option (Counter × Encoding)) :=
  honestly (layerSearch parameter data index lay)

noncomputable def finishCostSource (parameter : PublicParameter) (data : PublicData)
    (message : Message) (randomness : Randomness) : OracleComp CostSpec (Option Signature) := do
  let first ← HiddenCost.honest (Security.digestInput parameter data.root message randomness)
  let digest := truncateMessageDigest first
  let index := digestIndex digest
  let some found ← sequenceDep (α := fun _ => Counter × Encoding) (layerCostSearch parameter data index)
    | return none
  let values ← sequenceFin fun lay : Layer => sequenceFin fun chain => HiddenCost.reveal
    (.chain lay (treeIndexAt index lay) (leafIndexAt index lay) chain ((found lay).2 chain))
  let opening ← sequenceFin fun c => coordCostSource data index c (digestMarks digest c)
  return some ⟨randomness, opening, layerSignatures data index found values⟩

theorem fixed_layerCostSearch (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (data : PublicData) (table : HiddenGraph.Table) (index : Index) (lay : Layer) :
    simulateQ (fixedCostSource f table) (layerCostSearch parameter data index lay) =
      pure (firstEncoding f parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
        (data.keyMessage lay (treeIndexAt index lay) (leafIndexAt index lay)) encodingAttemptLimit 0) := by
  rw [layerCostSearch, fixedCostSource_honestly, layerSearch, ReferenceChoice.eval_search]

/-- Sequencing cost-level computations of fixed results. -/
theorem fixed_sequenceDep (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table) :
    ∀ {n : Nat} {α : Fin n → Type} (computation : (i : Fin n) → OracleComp CostSpec (Option (α i)))
      (results : (i : Fin n) → Option (α i)),
      (∀ i, simulateQ (fixedCostSource f table) (computation i) = pure (results i)) →
      simulateQ (fixedCostSource f table) (sequenceDep computation) = pure (Completeness.allSome results)
  | 0, _, _, _, _ => by
      simp only [sequenceDep, simulateQ_pure, Completeness.allSome]
      rw [dif_pos (fun i => Fin.elim0 i)]
      congr 2
      funext i
      exact i.elim0
  | n + 1, α, computation, results, h => by
      have ih := fixed_sequenceDep f table (α := fun i => α i.succ) (fun i => computation i.succ)
        (fun i => results i.succ) (fun i => h i.succ)
      rw [sequenceDep, simulateQ_bind, h 0, pure_bind]
      cases hhead : results 0 with
      | none =>
          simp only [simulateQ_pure]
          congr 1
          unfold Completeness.allSome
          rw [dif_neg (fun hall => by simpa [hhead] using hall 0)]
      | some head =>
          simp only [simulateQ_bind, ih, pure_bind]
          by_cases hall : ∀ i : Fin n, (results i.succ).isSome
          · have hsome : Completeness.allSome (fun i : Fin n => results i.succ) =
                some fun i => (results i.succ).get (hall i) := dif_pos hall
            have hall' : ∀ i : Fin (n + 1), (results i).isSome := by
              intro i
              refine Fin.cases ?_ (fun j => hall j) i
              simp [hhead]
            have hsome' : Completeness.allSome results = some fun i => (results i).get (hall' i) :=
              dif_pos hall'
            simp only [hsome, hsome', simulateQ_pure]
            congr 2
            funext i
            refine Fin.cases ?_ (fun j => ?_) i
            · simp [hhead]
            · simp
          · have hnone : Completeness.allSome (fun i : Fin n => results i.succ) = none := dif_neg hall
            have hnone' : Completeness.allSome results = none :=
              dif_neg (fun hall' => hall fun i => hall' i.succ)
            simp only [hnone, hnone', simulateQ_pure]

theorem fixed_layersCostSearch (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (data : PublicData) (table : HiddenGraph.Table) (index : Index) :
    simulateQ (fixedCostSource f table)
        (sequenceDep (α := fun _ => Counter × Encoding) (layerCostSearch parameter data index)) =
      pure (assembledEncodings f parameter data index) :=
  fixed_sequenceDep f table _ _ (fun lay => fixed_layerCostSearch f parameter data table index lay)

theorem fixed_finishCostSource (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (data : PublicData) (table : HiddenGraph.Table) (message : Message) (randomness : Randomness) :
    simulateQ (fixedCostSource f table) (finishCostSource parameter data message randomness) =
      pure (assembled f parameter data table message randomness) := by
  have hdigest : truncateMessageDigest (f (Security.digestInput parameter data.root message randomness)) =
      evalWithAnswerFn f (messageDigest parameter data.root message randomness :
        OracleComp HashSpec MessageDigest) := by
    simp only [messageDigest, messageDigestCall, oracleHash, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
    rfl
  simp only [finishCostSource, simulateQ_bind, fixedCostSource_honest, pure_bind]
  rw [hdigest, fixed_layersCostSearch, pure_bind]
  unfold assembled
  cases hs : assembledEncodings f parameter data
      (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root message randomness :
        OracleComp HashSpec MessageDigest))) with
  | none => simp only [hs, simulateQ_pure, Option.map_none]
  | some found =>
      have hvalues : simulateQ (fixedCostSource f table) (sequenceFin fun lay : Layer => sequenceFin fun chain =>
          HiddenCost.reveal (D := HashInput) (R := HashOutput)
            (.chain lay (treeIndexAt (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root
              message randomness : OracleComp HashSpec MessageDigest))) lay)
              (leafIndexAt (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root
                message randomness : OracleComp HashSpec MessageDigest))) lay) chain ((found lay).2 chain))) =
          pure (assembledValues table (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root
            message randomness : OracleComp HashSpec MessageDigest))) found) := by
        apply fixedCostSource_sequenceFin_pure
        intro lay
        exact fixedCostSource_sequence_reveal f table _
      simp only [hs, simulateQ_bind, hvalues, fixed_forestCostSource, pure_bind, simulateQ_pure,
        Option.map_some]

/-- The counted finish evaluates to the actual one, at no cost. -/
theorem finishCostSource_correct (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (table : HiddenGraph.Table)
    (hdata : DataCorrect f parameter seed data) (htable : CoordinatesCorrect f parameter seed table)
    (message : Message) (randomness : Randomness)
    (hland : Landed parameter (digestIndex (evalWithAnswerFn f
      (messageDigest parameter data.root message randomness : OracleComp HashSpec MessageDigest)))) :
    simulateQ (fixedCostSource f table) (finishCostSource parameter data message randomness) =
      pure (evalWithAnswerFn f (Seeded.finishSign ⟨seed, parameter, data.root⟩ message randomness)) := by
  rw [fixed_finishCostSource,
    eval_finishSign_assembled f parameter seed data table hdata htable message randomness hland]

/-- The scan from a start with a step: no randomness. -/
noncomputable def signCostSourceLoop (parameter : PublicParameter) (data : PublicData)
    (message : Message) (step : Randomness) : Nat → Randomness → OracleComp CostSpec (Option Signature)
  | 0, _ => pure none
  | attempts + 1, randomness => do
      let first ← HiddenCost.honest (Security.digestInput parameter data.root message randomness)
      if Landed parameter (blockIndex first) then
        finishCostSource parameter data message randomness
      else signCostSourceLoop parameter data message step attempts (randomness + step)

/-- The step of the walk of `message`. -/
def PublicData.step (data : PublicData) (message : Message) : Randomness := walkStep (data.steps message)

/-- One uniform start, then the scan with the message's step. -/
noncomputable def signCostSource (parameter : PublicParameter) (data : PublicData)
    (message : Message) : OracleComp CostSpec (Option Signature) := do
  let start ← liftM ($ᵗ Randomness : ProbComp Randomness)
  signCostSourceLoop parameter data message (data.step message) digestAttemptLimit start

end LeanForest.Security.GraphView

end

section

/-! The counted graph signer composed through an arbitrary adaptive adversary and the actual
verifier: explicit-reveal cost programs for the interaction, the rest of the game and the whole
game, which retain the strong signing log, and key generation on a fixed answer function. -/

open OracleComp OracleSpec
namespace LeanForest.Security.GraphView

variable [Params]
open Concrete Completeness Prefix HiddenGraph SeedCoupling
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] signCostSource Seeded.keygenFromSeed

def ordinaryCostSource : QueryImpl OracleWorld (OracleComp CostSpec)
  | .inl request => liftM (CostSpec.query (.inl (.inl request)))
  | .inr request => liftM (CostSpec.query (.inl (.inr (.inl request))))

theorem fixedCostSource_ordinary (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table)
    (request : OracleWorld.Domain) :
    simulateQ (fixedCostSource f table) (ordinaryCostSource request) = fixedWorldCost f request := by
  cases request <;> rw [ordinaryCostSource, simulateQ_spec_query] <;> rfl


noncomputable def costInteraction (parameter : PublicParameter) (data : PublicData) :
    QueryImpl (OracleWorld + SigningSpec) (WriterT (QueryLog SigningSpec) (OracleComp CostSpec)) :=
  ordinaryCostSource.liftTarget (WriterT (QueryLog SigningSpec) (OracleComp CostSpec)) +
    QueryImpl.withLogging (spec := SigningSpec) (m := OracleComp CostSpec)
      (fun message => signCostSource parameter data message)

noncomputable def costRest (parameter : PublicParameter) (data : PublicData) (adversary : Adversary) :
    OracleComp CostSpec Bool := do
  let pk : PublicKey := ⟨data.root, parameter⟩
  let (forgery, log) ← (simulateQ (costInteraction parameter data) (adversary.main pk)).run
  let verified ← liftM (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool)
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

/-- The game after key generation, which is free. -/
noncomputable def costGame (parameter : PublicParameter) (data : PublicData) (adversary : Adversary) :
    OracleComp CostSpec Bool :=
  costRest parameter data adversary

theorem eval_keygen_graph (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (hdata : DataCorrect f parameter seed data)
    (hparameter : evalWithAnswerFn f (deriveKey 0 .parameter seed : OracleComp HashSpec Digest) = parameter) :
    evalWithAnswerFn f (Seeded.keygenFromSeed seed) =
      ((⟨data.root, parameter⟩, ⟨seed, parameter, data.root⟩) : PublicKey × Seeded.SecretKey) := by
  simp only [Seeded.keygenFromSeed, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    hparameter, ← hdata.root]

end LeanForest.Security.GraphView

end
