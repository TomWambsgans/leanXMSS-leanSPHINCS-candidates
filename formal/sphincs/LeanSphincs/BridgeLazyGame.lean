import LeanSphincs.BridgeShortCost

/-! The seed-free experiment is bounded by the stopped hidden-row experiment with an actual
lazy outside random oracle started from the structural cache. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.HiddenBridge

open Completeness SeedModel Graph Assembly Reduce HiddenGraph Eager Internalize

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

theorem evalDist_stoppedExperiment_lazy {A α : Type}
    (model : HiddenRows.Model HashInput HashOutput A HiddenGraph.Coordinate)
    (cache : QueryCache HashSpec)
    (computation : OracleComp (HiddenRows.SourceSpec HashInput HashOutput HiddenGraph.Coordinate) α)
    (hshort : OnlyShort computation) (known : HiddenReveal.Knowledge HiddenGraph.Coordinate) :
    𝒟[($ᵗ Eager.Table) >>= fun outside =>
        HiddenRows.stoppedExperiment model (extend cache outside) computation known] =
      𝒟[Option.map Prod.fst <$> HiddenOutside.stoppedExperiment model computation known cache] := by
  unfold HiddenRows.stoppedExperiment HiddenOutside.stoppedExperiment
  rw [evalDist_bind_bind_swap, map_bind, evalDist_bind, evalDist_bind]
  congr 1
  funext table
  exact evalDist_stopped_lazy model table computation hshort known cache

theorem probEvent_bind_congr₂ {α β γ : Type} (p : ProbComp α) (k₁ : α → ProbComp β)
    (k₂ : α → ProbComp γ) (event₁ : β → Prop) (event₂ : γ → Prop)
    (h : ∀ a, Pr[event₁ | k₁ a] = Pr[event₂ | k₂ a]) :
    Pr[event₁ | p >>= k₁] = Pr[event₂ | p >>= k₂] := by
  simp only [probEvent_bind_eq_tsum, h]

variable [Params]

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

/-- **Seed-free to lazy stopped.** -/
theorem seedFree_le_lazy (adversary : Adversary) (q : Nat)
    (event : Option Bool × List (HiddenCost.Entry HashInput) → Prop) :
    Pr[event | seedFreeExperiment (internalize adversary) q] ≤
      Pr[HiddenReveal.StopOr (event ∘ Prod.fst) | do
        let parameterOutput ← $ᵗ HashOutput
        let fixed ← $ᵗ HiddenGraph.Table
        let highs ← $ᵗ CoordinateHighs
        let remaining ← $ᵗ RemainingOutputs
        HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
          (HiddenCost.erase (HiddenCost.trace
            (sampleProgram (internalize adversary) q parameterOutput fixed highs remaining)))
          (knownOf (truncateHash parameterOutput) fixed)
          (structCache (splitMaterial parameterOutput highs remaining fixed)
            (splitAnswers highs remaining fixed))] := by
  refine (seedFree_le_stopped (internalize adversary) q event).trans (le_of_eq ?_)
  refine probEvent_bind_congr₂ _ _ _ _ _ fun parameterOutput => ?_
  refine probEvent_bind_congr₂ _ _ _ _ _ fun fixed => ?_
  refine probEvent_bind_congr₂ _ _ _ _ _ fun highs => ?_
  refine probEvent_bind_congr₂ _ _ _ _ _ fun remaining => ?_
  have hshort : OnlyShort (HiddenCost.erase (HiddenCost.trace
      (sampleProgram (internalize adversary) q parameterOutput fixed highs remaining))) :=
    OnlyC.erase (OnlyC.trace (OnlyC.cap (OnlyC.costGame (truncateHash parameterOutput)
      (GraphView.publicData (labelsOf (splitMaterial parameterOutput highs remaining fixed)
        (splitAnswers highs remaining fixed))) adversary) q))
  unfold outsideFn
  rw [probEvent_congr' (fun _ _ => Iff.rfl)
    (evalDist_stoppedExperiment_lazy (sampleModel parameterOutput highs) _ _ hshort _),
    probEvent_stopOr_map]
end LeanSphincs.Security.HiddenBridge
