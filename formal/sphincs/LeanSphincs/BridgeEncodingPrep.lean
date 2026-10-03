import LeanSphincs.BridgeSupport

/-! Every canonical WOTS encoding-search input of the candidate key is answered from an
independent pre-sampled table placed in the lazy outside oracle's initial cache. Encoding
targets are then fixed before the run. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.HiddenBridge

open Eager Short HiddenCost Concrete

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- Every leaf's canonical WOTS encoding search of its FORS key, run in order. -/
def searchAll (parameter : PublicParameter) (forsKey : Index → Digest) :
    OracleComp HashSpec (Index → Option (Counter × Encoding)) :=
  Concrete.sequenceFin fun leaf => ReferenceChoice.search parameter topLayer rootTree leaf (forsKey leaf)
    encodingAttemptLimit 0

theorem Only.searchAll (parameter : PublicParameter) (forsKey : Index → Digest) :
    Short.Only (searchAll parameter forsKey) :=
  Short.Only.sequenceFin _ fun _ => Only.search _ _ _ _ _ _ _

/-- Running any short hash computation on the lazy oracle first, then sampling the remaining
table, is the eager table itself. Only the resulting cache is kept. -/
theorem evalDist_eager_prefix {β γ : Type} (computation : OracleComp HashSpec γ)
    (hshort : Short.Only computation) (cache : QueryCache HashSpec)
    (next : (HashInput → HashOutput) → ProbComp β) :
    𝒟[($ᵗ Eager.Table) >>= fun outside => next (extend cache outside)] =
      𝒟[(simulateQ randomOracle computation).run cache >>= fun result =>
        ($ᵗ Eager.Table) >>= fun outside => next (extend result.2 outside)] := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  | query_bind input next' ih =>
      rw [Short.Only, isQueryBoundP_query_bind_iff] at hshort
      have hnext : ∀ answer, Short.Only (next' answer) := fun answer => by
        have := hshort.2 answer
        split at this <;> simpa [Short.Only] using this
      have hinput : IsShort input := by
        rcases hshort.1 with hnot | hzero
        · exact Classical.not_not.mp hnot
        · omega
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
      change _ = 𝒟[(randomOracle (spec := HashSpec) input).run cache >>= _]
      cases hc : cache input with
      | some answer =>
          rw [QueryImpl.withCaching_run_some _ hc, pure_bind]
          exact ih answer (hnext answer) cache
      | none =>
          rw [QueryImpl.withCaching_run_none _ hc, bind_map_left]
          have hupdate : ∀ (answer : HashOutput) (outside : Eager.Table),
              next (extend (cache.cacheQuery input answer) outside) =
                (fun table => next (extend cache table)) (Function.update outside ⟨input, hinput⟩ answer) := by
            intro answer outside
            simp only [extend_cacheQuery cache outside hinput hc answer]
          calc 𝒟[($ᵗ Eager.Table) >>= fun outside => next (extend cache outside)]
              = 𝒟[(($ᵗ HashOutput : ProbComp HashOutput) >>= fun answer => ($ᵗ Eager.Table) >>=
                  fun outside => pure (Function.update outside ⟨input, hinput⟩ answer)) >>=
                    fun outside => next (extend cache outside)] := by
                symm
                rw [evalDist_bind, evalDist_uniformSample_bind_update (D := ShortIn) (R := HashOutput)
                  ⟨input, hinput⟩, ← evalDist_bind]
            _ = 𝒟[($ᵗ HashOutput : ProbComp HashOutput) >>= fun answer => ($ᵗ Eager.Table) >>= fun outside =>
                  next (extend (cache.cacheQuery input answer) outside)] := by
                simp only [bind_assoc, pure_bind, hupdate]
            _ = _ := by
                change _ = 𝒟[uniformSampleImpl (spec := HashSpec) input >>= _]
                apply evalDist_bind_congr'
                intro answer
                exact ih answer (hnext answer) _

theorem evalDist_stoppedExperiment_prep {A α : Type}
    (model : HiddenRows.Model HashInput HashOutput A HiddenGraph.Coordinate)
    (base : QueryCache HashSpec) (parameter : PublicParameter) (forsKey : Index → Digest)
    (computation : OracleComp (HiddenRows.SourceSpec HashInput HashOutput HiddenGraph.Coordinate) α)
    (hshort : OnlyShort computation) (known : HiddenReveal.Knowledge HiddenGraph.Coordinate) :
    𝒟[($ᵗ Eager.Table) >>= fun outside =>
        HiddenRows.stoppedExperiment model (extend base outside) computation known] =
      𝒟[(simulateQ randomOracle (searchAll parameter forsKey)).run base >>= fun prepared =>
        Option.map Prod.fst <$> HiddenOutside.stoppedExperiment model computation known prepared.2] := by
  rw [evalDist_eager_prefix (searchAll parameter forsKey) (Only.searchAll parameter forsKey) base
    (fun outside => HiddenRows.stoppedExperiment model outside computation known)]
  apply evalDist_bind_congr'
  intro prepared
  exact evalDist_stoppedExperiment_lazy model _ computation hshort known

section Game

open Completeness SeedModel Graph Assembly Reduce HiddenGraph Internalize GraphView

variable [Params]

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

/-- The preparation run of one sample: every canonical encoding search, started from the
structural cache. -/
noncomputable def preparation (parameterOutput : HashOutput) (fixed : HiddenGraph.Table)
    (highs : CoordinateHighs) (remaining : RemainingOutputs) :
    ProbComp ((Index → Option (Counter × Encoding)) × QueryCache HashSpec) :=
  (simulateQ randomOracle (searchAll (truncateHash parameterOutput)
    (sampleData parameterOutput fixed highs remaining).forsKey)).run
    (structCache (splitMaterial parameterOutput highs remaining fixed) (splitAnswers highs remaining fixed))

/-- **The actual advantage in the stopped prepared world.** -/
theorem forgeAdvantage_le_prep (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound adversary q) :
    forgeAdvantage adversary ≤
      Pr[HiddenReveal.StopOr RichWin | do
        let parameterOutput ← $ᵗ HashOutput
        let fixed ← $ᵗ HiddenGraph.Table
        let highs ← $ᵗ CoordinateHighs
        let remaining ← $ᵗ RemainingOutputs
        let prepared ← preparation parameterOutput fixed highs remaining
        HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
          (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
            (sampleData parameterOutput fixed highs remaining))))
          (knownOf (truncateHash parameterOutput) fixed) prepared.2] + q / (2 : ℝ≥0∞) ^ 256 := by
  refine (forgeAdvantage_le_seedFree adversary q hbound).trans (add_le_add ?_ le_rfl)
  refine (seedFree_le_stopped (internalize adversary) q Win).trans (le_of_eq ?_)
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
    (evalDist_stoppedExperiment_prep (sampleModel parameterOutput highs) _ (truncateHash parameterOutput)
      (sampleData parameterOutput fixed highs remaining).forsKey _ hshort _)]
  refine probEvent_bind_congr₂ _ _ _ _ _ fun prepared => ?_
  rw [probEvent_stopOr_map]
  unfold HiddenOutside.stoppedExperiment
  refine probEvent_bind_congr₂ _ _ _ _ _ fun table => ?_
  have hprog : sampleProgram (internalize adversary) q parameterOutput fixed highs remaining =
      (fun result => Option.map outcomeWins result.1) <$> richProgram (internalize adversary) q
        (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining) :=
    cap_costGame_eq _ _ _ _
  rw [hprog, trace_map, erase_map, outside_stopped_map, probEvent_stopOr_map]
  have hevent : (HiddenReveal.StopOr ((Win ∘ Prod.fst) ∘ fun result :
      ((Option Outcome × List HiddenGraph.Coordinate) × List (Entry HashInput)) × QueryCache HashSpec =>
        ((Option.map outcomeWins result.1.1.1, result.1.2), result.2))) =
      HiddenReveal.StopOr RichWin := by
    funext result
    rcases result with _ | ⟨⟨⟨outcome, reveals⟩, entries⟩, cache⟩
    · rfl
    · rcases outcome with _ | value <;> simp [HiddenReveal.StopOr, Win, RichWin]
  rw [hevent]

end Game

end LeanSphincs.Security.HiddenBridge
