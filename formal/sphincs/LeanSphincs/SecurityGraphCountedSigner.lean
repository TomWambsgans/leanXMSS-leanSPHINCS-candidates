import LeanSphincs.SecurityGraphCost
import LeanSphincs.SecurityPrefixErasedGame

/-! The graph-reveal signer preserves the joint law of the actual signature and its
original hash cost. Internal graph work is charged even when encoding exhausts. -/

open OracleComp OracleSpec

namespace LeanSphincs.Security.GraphView
open Concrete Completeness Prefix HiddenGraph
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] firstEncoding ReferenceChoice.search encodingAttemptLimit
  Randomized.finishSign digestAttemptLimit sequenceFin

abbrev CostSpec := HiddenCost.SourceCostSpec HashInput HashOutput Coordinate

noncomputable def fixedCostSource (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table) :
    QueryImpl CostSpec (AddWriterT Nat PMF) :=
  QueryImpl.withAddCost (spec := CostSpec)
    (fun | .inl request => fixedSource f table request | .inr _ => PMF.pure ())
    HiddenCost.sourceCost

theorem fixedCostSource_lift_hash (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table)
    {α : Type} (computation : OracleComp HashSpec α) :
    simulateQ (fixedCostSource f table) (liftM computation : OracleComp CostSpec α) =
      simulateQ (fixedWorldCost f) (liftM computation : OracleComp OracleWorld α) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [liftM_pure, simulateQ_pure]
  | query_bind input next ih =>
      simp only [liftM_bind, simulateQ_bind, ih]
      rfl

theorem fixedCostSource_lift_prob (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table)
    {α : Type} (computation : ProbComp α) :
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
      simulateQ (fixedHashWorld f) (SphincsSecurity.QueryCap.counted SourceHash
        (liftM computation : OracleComp OracleWorld α)) := by
    rw [SphincsSecurity.QueryCap.simulate_withCost]
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

theorem fixedCostSource_tick (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table)
    (amount : Nat) :
    simulateQ (fixedCostSource f table)
      (HiddenCost.tick (D := HashInput) (R := HashOutput) (ι := Coordinate) amount) =
      AddWriterT.addTell amount := by
  rw [HiddenCost.tick, simulateQ_spec_query]
  apply WriterT.ext
  simp [fixedCostSource, QueryImpl.withAddCost, QueryImpl.withCost,
    HiddenCost.sourceCost, AddWriterT.addTell]
  simp only [← PMF.monad_pure_eq_pure, map_pure]

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

variable [Params]

noncomputable def finishCostSource (parameter : PublicParameter) (data : PublicData)
    (message : Message) (randomness : Randomness) : OracleComp CostSpec (Option Signature) := do
  let digest ← liftM (messageDigest parameter data.root message randomness :
    OracleComp HashSpec MessageDigest)
  HiddenCost.tick 147145
  let index := digestIndex digest
  let some (counter, word) ← liftM (ReferenceChoice.search parameter topLayer rootTree index
    (data.forsKey index) encodingAttemptLimit 0) | return none
  let values ← sequenceFin fun chain => HiddenCost.reveal
    (.chain topLayer rootTree index chain (word chain))
  let secrets ← sequenceFin fun tree => HiddenCost.reveal
    (.ftsSecret index tree (digestLeaves digest tree))
  HiddenCost.tick (184 + treePathCost)
  let top : LayerSignature topLayer := ⟨counter, values, data.treePath index⟩
  return some ⟨randomness, secrets, data.forsPath index (digestLeaves digest),
    Fin.cases top (fun i => Fin.elim0 i)⟩

theorem fixed_finishCostSource (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (data : PublicData) (table : HiddenGraph.Table) (message : Message) (randomness : Randomness) :
    simulateQ (fixedCostSource f table) (finishCostSource parameter data message randomness) =
      WriterT.mk (PMF.pure (assembled f parameter data table message randomness,
        Multiplicative.ofAdd (finishHashCost f parameter data message randomness))) := by
  simp only [finishCostSource, simulateQ_bind, fixedCostSource_lift_hash,
    fixedWorldCost_lift_hash, fixedCostSource_tick]
  apply WriterT.ext
  simp only [WriterT.run_bind, WriterT.run_mk, AddWriterT.run_addTell,
    ← PMF.monad_pure_eq_pure, pure_bind, assembled, finishHashCost,
    ReferenceChoice.eval_search, hashCalls_messageDigest]
  cases hs : firstEncoding f parameter topLayer rootTree
      (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root message randomness :
        OracleComp HashSpec MessageDigest)))
      (data.forsKey (digestIndex (evalWithAnswerFn f
        (messageDigest parameter data.root message randomness : OracleComp HashSpec MessageDigest))))
      encodingAttemptLimit 0 with
  | none =>
      simp only [simulateQ_pure, WriterT.run_pure, Option.map_none, Option.isSome_none,
        Bool.false_eq_true, ↓reduceIte, Nat.add_zero, map_pure, mul_one]
      simp only [← ofAdd_add, ← Nat.add_assoc]
  | some pair =>
      obtain ⟨counter, word⟩ := pair
      simp only [simulateQ_bind, fixedCostSource_sequence_reveal, pure_bind,
        fixedCostSource_tick, simulateQ_pure, WriterT.run_bind, WriterT.run_pure,
        AddWriterT.run_addTell, ← PMF.monad_pure_eq_pure, pure_bind,
        Option.map_some, Option.isSome_some, ↓reduceIte, map_pure, mul_one]
      simp only [← ofAdd_add, ← Nat.add_assoc]

theorem finishCostSource_correct (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (table : HiddenGraph.Table)
    (hdata : DataCorrect f parameter seed data) (htable : CoordinatesCorrect f parameter seed table)
    (message : Message) (randomness : Randomness)
    (hland : Landed parameter (digestIndex (evalWithAnswerFn f
      (messageDigest parameter data.root message randomness : OracleComp HashSpec MessageDigest)))) :
    simulateQ (fixedCostSource f table) (finishCostSource parameter data message randomness) =
      simulateQ (fixedWorldCost f)
        (liftM (Randomized.finishSign ⟨seed, parameter, data.root⟩ message randomness) :
          OracleComp OracleWorld (Option Signature)) := by
  rw [fixed_finishCostSource, fixedWorldCost_lift_hash,
    eval_finishSign_assembled f parameter seed data table hdata htable message randomness hland,
    hashCalls_finishSign_exact f parameter seed data hdata]

noncomputable def signCostSourceLoop (parameter : PublicParameter) (data : PublicData)
    (message : Message) : Nat → OracleComp CostSpec (Option Signature)
  | 0 => pure none
  | attempts + 1 => do
      let randomness ← liftM ($ᵗ Randomness : ProbComp Randomness)
      let first ← liftM (messageDigestCall parameter data.root message randomness 0 :
        OracleComp HashSpec HashOutput)
      if Landed parameter (blockIndex first) then
        finishCostSource parameter data message randomness
      else signCostSourceLoop parameter data message attempts

theorem fixed_signCostSourceLoop (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (table : HiddenGraph.Table)
    (hdata : DataCorrect f parameter seed data) (htable : CoordinatesCorrect f parameter seed table)
    (message : Message) (attempts : Nat) :
    simulateQ (fixedCostSource f table) (signCostSourceLoop parameter data message attempts) =
      simulateQ (fixedWorldCost f) (do
        let some randomness ← Randomized.signDigestLoop ⟨seed, parameter, data.root⟩ message attempts
          | return none
        liftM (Randomized.finishSign ⟨seed, parameter, data.root⟩ message randomness)) := by
  induction attempts with
  | zero => simp only [signCostSourceLoop, Randomized.signDigestLoop, pure_bind, simulateQ_pure]
  | succ attempts ih =>
      simp only [signCostSourceLoop, Randomized.signDigestLoop, bind_assoc, simulateQ_bind,
        fixedCostSource_lift_prob, fixedCostSource_lift_hash, fixedWorldCost_lift_hash]
      apply bind_congr
      intro randomness
      simp only [hashCalls_signAttempt, hashCalls_messageDigestCall]
      apply WriterT.ext
      simp only [WriterT.run_bind, WriterT.run_mk, ← PMF.monad_pure_eq_pure, pure_bind,
        Seeded.signAttempt, evalWithAnswerFn_bind, evalWithAnswerFn_pure, hashCalls_signAttempt]
      by_cases hland : Landed parameter (blockIndex (evalWithAnswerFn f
        (messageDigestCall parameter data.root message randomness 0 : OracleComp HashSpec HashOutput)))
      · have hland' : Landed parameter (digestIndex (evalWithAnswerFn f
            (messageDigest parameter data.root message randomness : OracleComp HashSpec MessageDigest))) := by
          simpa only [messageDigest, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
            digestIndex_truncate] using hland
        simp only [hland, ↓reduceIte, evalWithAnswerFn_pure, simulateQ_pure, pure_bind,
          finishCostSource_correct f parameter seed data table hdata htable message randomness hland',
          WriterT.run_pure, ← PMF.monad_pure_eq_pure, pure_bind, one_mul,
          Prod.mk.eta, Functor.map_id]
        rw [Functor.map_map]
      · simp only [hland, ↓reduceIte, evalWithAnswerFn_pure, simulateQ_pure, pure_bind]
        rw [ih]
        simp only [simulateQ_bind, WriterT.run_bind]

noncomputable def signCostSource (parameter : PublicParameter) (data : PublicData)
    (message : Message) : OracleComp CostSpec (Option Signature) :=
  signCostSourceLoop parameter data message digestAttemptLimit

/-- Both searches, including exhaustion, preserve the joint output and original-cost law. -/
theorem signCostSource_correct (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (table : HiddenGraph.Table)
    (hdata : DataCorrect f parameter seed data) (htable : CoordinatesCorrect f parameter seed table)
    (message : Message) :
    simulateQ (fixedCostSource f table) (signCostSource parameter data message) =
      simulateQ (fixedWorldCost f) (Randomized.sign ⟨seed, parameter, data.root⟩ message) :=
  fixed_signCostSourceLoop f parameter seed data table hdata htable message digestAttemptLimit

end LeanSphincs.Security.GraphView
