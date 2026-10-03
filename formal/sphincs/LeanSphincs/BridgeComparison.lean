import LeanSphincs.BridgeEncodingPrep
import LeanSphincs.SecurityHiddenDeferred

/-! The common stop/comparison bound with a terminal bad event that may depend on the
whole hidden coordinate table. The table is sampled first; for each fixed table the stopped
run agrees with the forced-failure comparison until its first hidden hit. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable {ι : Type} [Fintype ι]
noncomputable local instance : DecidableEq ι := Classical.decEq ι

/-- For a fixed table, a stopped run either stops or behaves as the comparison. -/
theorem run_stopOr_le {α : Type} (table : ι → Digest) (computation : OracleComp (ViewSpec ι) α)
    (known : Knowledge ι) (bad : α → Prop) :
    Pr[StopOr bad | run table computation known] ≤
      Pr[= none | run table computation known] +
        Pr[fun result => bad result.1 | fixedComparison table computation known] := by
  induction computation using OracleComp.inductionOn generalizing known with
  | pure value =>
      rw [run_pure, fixedComparison_pure]
      by_cases hb : bad value <;> simp [StopOr, hb]
  | query_bind input next ih =>
      rcases input with draw | (coordinate | guess)
      · rw [run_private, fixedComparison_private]
        simp only [probEvent_bind_eq_tsum, ← probEvent_eq_eq_probOutput]
        rw [← ENNReal.tsum_add]
        refine ENNReal.tsum_le_tsum fun value => ?_
        rw [← mul_add]
        exact mul_le_mul' le_rfl (by simpa only [probEvent_eq_eq_probOutput] using ih value known)
      · rw [run_reveal, fixedComparison_reveal]
        exact ih _ _
      · rw [run_guess, fixedComparison_guess, probEvent_map]
        by_cases hhit : known guess.1 = none ∧ table guess.1 = guess.2
        · rw [if_pos hhit]
          simp [StopOr]
        · rw [if_neg hhit]
          exact ih () known

end LeanSphincs.Security.HiddenReveal

namespace LeanSphincs.Security.HiddenOutside

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
noncomputable local instance : DecidableEq D := Classical.decEq _
noncomputable local instance : DecidableEq ι := Classical.decEq _

/-- **Table-dependent common bound.** Stopping and a terminal event that may read the whole
hidden table are charged to the forced-failure comparison run against that same table. -/
theorem table_stop_or_bad_bound {α : Type} (model : HiddenRows.Model D R A ι)
    (computation : OracleComp (HiddenRows.SourceSpec D R ι) α)
    (known : HiddenReveal.Knowledge ι) (cache : Cache D R)
    (bad : (ι → Digest) → α × Cache D R → Prop) :
    Pr[fun pair => HiddenReveal.StopOr (bad pair.1) pair.2 |
        HiddenReveal.completion known >>= fun table =>
          (fun result => (table, result)) <$> stopped model table computation known cache] ≤
      HiddenReveal.expectedGuessCharge (compile model computation known cache) known / (2 : ℝ≥0∞) ^ 128 +
        Pr[fun pair => bad pair.1 pair.2.1 |
          HiddenReveal.completion known >>= fun table =>
            (fun result => (table, result)) <$>
              HiddenReveal.fixedComparison table (compile model computation known cache) known] := by
  refine le_trans ?_ (add_le_add (HiddenReveal.adaptive_guess_bound_charge _ known) le_rfl)
  unfold HiddenReveal.experiment
  unfold HiddenReveal.completion
  simp only [bind_map_left, probEvent_bind_eq_tsum, probEvent_map, probOutput_bind_eq_tsum]
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun fresh => ?_
  rw [← mul_add]
  refine mul_le_mul' le_rfl ?_
  rw [← run_compile model _ computation known cache (HiddenRows.knownAgrees_completion known fresh)]
  exact HiddenReveal.run_stopOr_le (tableExtending known fresh) _ known (bad (tableExtending known fresh))

end LeanSphincs.Security.HiddenOutside
