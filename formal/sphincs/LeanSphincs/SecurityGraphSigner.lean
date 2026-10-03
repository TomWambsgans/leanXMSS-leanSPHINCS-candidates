import LeanSphincs.SecurityGraphView
import LeanSphincs.SecurityPrefixFullSign

/-! The complete randomized signer as an explicit coordinate-reveal program. Randomizer
draws retain replacement and exhaustion, and the output law equals the actual signer.
Original-cost preservation is handled separately. -/

open OracleComp OracleSpec

namespace LeanSphincs.Security.GraphView
open Concrete Completeness Prefix HiddenGraph
attribute [local instance] Classical.propDecidable
attribute [local irreducible] finishSource Randomized.finishSign digestAttemptLimit
set_option backward.isDefEq.respectTransparency false

noncomputable def fixedSource (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table) :
    QueryImpl HiddenGraph.SourceSpec PMF :=
  (fun input => PMF.uniformOfFintype (unifSpec.Range input) : QueryImpl unifSpec PMF) +
    (fixedView f table).liftTarget PMF

theorem fixedSource_lift_view (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table)
    {α : Type} (computation : OracleComp HashViewSpec α) :
    simulateQ (fixedSource f table) (liftM computation : OracleComp HiddenGraph.SourceSpec α) =
      PMF.pure (evalWithAnswerFn (fixedView f table) computation) := by
  rw [fixedSource, QueryImpl.simulateQ_add_liftM_right, simulateQ_liftTarget]
  rfl

theorem fixedSource_lift_hash (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table)
    {α : Type} (computation : OracleComp HashSpec α) :
    simulateQ (fixedSource f table) (liftM computation : OracleComp HiddenGraph.SourceSpec α) =
      PMF.pure (evalWithAnswerFn f computation) := by
  change simulateQ (fixedSource f table)
    (liftM (liftM computation : OracleComp HashViewSpec α) : OracleComp HiddenGraph.SourceSpec α) = _
  rw [fixedSource_lift_view, eval_lift_hash]

theorem fixedSource_lift_prob (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table)
    {α : Type} (computation : ProbComp α) :
    simulateQ (fixedSource f table) (liftM computation : OracleComp HiddenGraph.SourceSpec α) =
      simulateQ (fixedHashWorld f) (liftM computation : OracleComp OracleWorld α) := by
  rw [fixedSource, QueryImpl.simulateQ_add_liftM_left]
  symm
  exact QueryImpl.simulateQ_liftComp_left_eq_of_apply (fixedHashWorld f)
    (fun input => PMF.uniformOfFintype (unifSpec.Range input)) (fun _ => rfl) computation

variable [Params]

noncomputable def signSourceLoop (parameter : PublicParameter) (data : PublicData)
    (message : Message) : Nat → OracleComp HiddenGraph.SourceSpec (Option Signature)
  | 0 => pure none
  | attempts + 1 => do
      let randomness ← liftM ($ᵗ Randomness : ProbComp Randomness)
      let first ← liftM (messageDigestCall parameter data.root message randomness 0 :
        OracleComp HashSpec HashOutput)
      if Landed parameter (blockIndex first) then
        liftM (finishSource parameter data message randomness)
      else signSourceLoop parameter data message attempts

theorem fixed_signSourceLoop (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (table : HiddenGraph.Table)
    (hdata : DataCorrect f parameter seed data) (htable : CoordinatesCorrect f parameter seed table)
    (message : Message) (attempts : Nat) :
    simulateQ (fixedSource f table) (signSourceLoop parameter data message attempts) =
      simulateQ (fixedHashWorld f) (do
        let some randomness ← Randomized.signDigestLoop ⟨seed, parameter, data.root⟩ message attempts
          | return none
        liftM (Randomized.finishSign ⟨seed, parameter, data.root⟩ message randomness)) := by
  induction attempts with
  | zero => simp only [signSourceLoop, Randomized.signDigestLoop, pure_bind, simulateQ_pure]
  | succ attempts ih =>
      simp only [signSourceLoop, Randomized.signDigestLoop, bind_assoc, simulateQ_bind,
        fixedSource_lift_prob, fixedSource_lift_hash, fixedHashWorld_lift_hash]
      apply bind_congr
      intro randomness
      simp only [← PMF.monad_pure_eq_pure, pure_bind, Seeded.signAttempt, evalWithAnswerFn_bind,
        evalWithAnswerFn_pure]
      by_cases hland : Landed parameter (blockIndex (evalWithAnswerFn f
        (messageDigestCall parameter data.root message randomness 0 : OracleComp HashSpec HashOutput)))
      · simp only [hland, ↓reduceIte, evalWithAnswerFn_pure, simulateQ_pure, pure_bind]
        rw [fixedSource_lift_view, fixedHashWorld_lift_hash]
        apply congrArg PMF.pure
        apply finishSource_correct f parameter seed data table hdata htable message randomness
        simpa only [messageDigest, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
          digestIndex_truncate] using hland
      · simp only [hland, ↓reduceIte, evalWithAnswerFn_pure, simulateQ_pure, pure_bind]
        simpa only [simulateQ_bind] using ih

noncomputable def signSource (parameter : PublicParameter) (data : PublicData) (message : Message) :
    OracleComp HiddenGraph.SourceSpec (Option Signature) :=
  signSourceLoop parameter data message digestAttemptLimit

/-- The actual signer and the explicit reveal frontend have exactly the same private-sample
distribution. This equality includes both searches' failure branches. -/
theorem signSource_correct (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (table : HiddenGraph.Table)
    (hdata : DataCorrect f parameter seed data) (htable : CoordinatesCorrect f parameter seed table)
    (message : Message) :
    simulateQ (fixedSource f table) (signSource parameter data message) =
      simulateQ (fixedHashWorld f) (Randomized.sign ⟨seed, parameter, data.root⟩ message) := by
  exact fixed_signSourceLoop f parameter seed data table hdata htable message digestAttemptLimit

end LeanSphincs.Security.GraphView
