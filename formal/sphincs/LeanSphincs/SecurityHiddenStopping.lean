import LeanSphincs.SecurityHiddenAccounting

/-! A common-comparison fundamental lemma: hidden-input stopping and an arbitrary terminal
bad event are charged together. Later seed/output/message monitors are measured on the same
forced-failure comparison, so they need not be evaluated in the stopped real execution. -/

open OracleComp OracleSpec ENNReal
namespace LeanSphincs.Security.HiddenReveal
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 100000
attribute [local instance] Classical.propDecidable
variable {ι : Type} [Fintype ι]
noncomputable local instance : DecidableEq ι := Classical.decEq _

def StopOr {α : Type} (bad : α → Prop) : Option α → Prop
  | none => True
  | some value => bad value

noncomputable def comparisonRisk {α : Type} (computation : OracleComp (ViewSpec ι) α)
    (known : Knowledge ι) (bad : α → Prop) : ℝ≥0∞ :=
  expectedGuessCharge computation known / (2 : ℝ≥0∞) ^ 128 +
    Pr[fun result => bad result.1 | comparison computation known]

theorem risk_private {α : Type} (draw : unifSpec.Domain)
    (next : unifSpec.Range draw → OracleComp (ViewSpec ι) α) (known : Knowledge ι) (bad : α → Prop) :
    comparisonRisk (liftM ((ViewSpec ι).query (.inl draw)) >>= next) known bad =
      ∑' value, Pr[= value | (liftM (unifSpec.query draw) : ProbComp _)] *
        comparisonRisk (next value) known bad := by
  rw [comparisonRisk, charge_private]
  change (∑' value, _ * _) / (2 : ℝ≥0∞) ^ 128 +
    Pr[fun result => bad result.1 | liftM (unifSpec.query draw) >>= fun value => comparison (next value) known] = _
  rw [probEvent_bind_eq_tsum]
  simp only [comparisonRisk, mul_add, div_eq_mul_inv, ← ENNReal.tsum_mul_right,
    ← ENNReal.tsum_add, mul_assoc]

theorem risk_reveal {α : Type} (coordinate : ι)
    (next : Digest → OracleComp (ViewSpec ι) α) (known : Knowledge ι) (bad : α → Prop) :
    comparisonRisk (liftM ((ViewSpec ι).query (.inr (.inl coordinate))) >>= next) known bad =
      ∑' result, Pr[= result | (randomOracle (spec := ι →ₒ Digest) coordinate).run known] *
        comparisonRisk (next result.1) result.2 bad := by
  rw [comparisonRisk, charge_reveal]
  change (∑' result, _ * _) / (2 : ℝ≥0∞) ^ 128 +
    Pr[fun result => bad result.1 | (randomOracle (spec := ι →ₒ Digest) coordinate).run known >>=
      fun result => comparison (next result.1) result.2] = _
  rw [probEvent_bind_eq_tsum]
  simp only [comparisonRisk, mul_add, div_eq_mul_inv, ← ENNReal.tsum_mul_right,
    ← ENNReal.tsum_add, mul_assoc]

theorem risk_guess {α : Type} (guess : ι × Digest) (next : Unit → OracleComp (ViewSpec ι) α)
    (known : Knowledge ι) (bad : α → Prop) :
    comparisonRisk (liftM ((ViewSpec ι).query (.inr (.inr guess))) >>= next) known bad =
      (if known guess.1 = none then 1 / (2 : ℝ≥0∞) ^ 128 else 0) +
        comparisonRisk (next ()) known bad := by
  rw [comparisonRisk, charge_guess]
  change ((if known guess.1 = none then 1 else 0) + _) / (2 : ℝ≥0∞) ^ 128 +
    Pr[fun result => bad result.1 | (fun result =>
      (result.1, (if known guess.1 = none then 1 else 0) + result.2)) <$> comparison (next ()) known] = _
  rw [probEvent_map, ENNReal.add_div]
  simp only [comparisonRisk, ite_div, ENNReal.zero_div, add_assoc]
  rfl

private theorem revealed_cache (known : Knowledge ι) (coordinate : ι)
    (result : Digest × Knowledge ι)
    (hr : result ∈ support ((randomOracle (spec := ι →ₒ Digest) coordinate).run known)) :
    result.2 = known.cacheQuery coordinate result.1 := by
  cases hc : known coordinate with
  | none =>
      rw [QueryImpl.withCaching_run_none _ hc, support_map] at hr
      obtain ⟨value, _, rfl⟩ := hr
      rfl
  | some value =>
      rw [QueryImpl.withCaching_run_some _ hc, support_pure, Set.mem_singleton_iff] at hr
      subst result
      apply QueryCache.ext
      intro other
      by_cases ho : other = coordinate
      · subst other; simp [hc]
      · simp [QueryCache.cacheQuery_of_ne _ _ ho]

/-- Stopping at a hidden match and every terminal bad event are bounded on one comparison.
The comparison's terminal event can include its complete query/cost transcript. -/
theorem stop_or_bad_bound {α : Type} (computation : OracleComp (ViewSpec ι) α)
    (known : Knowledge ι) (bad : α → Prop) :
    Pr[StopOr bad | experiment computation known] ≤ comparisonRisk computation known bad := by
  induction computation using OracleComp.inductionOn generalizing known with
  | pure value =>
      simp only [experiment, run_pure, comparisonRisk, charge_pure, ENNReal.zero_div, zero_add,
        comparison, OracleComp.construct_pure, probEvent_pure]
      by_cases hb : bad value
      · simp only [hb, ↓reduceIte]; exact probEvent_le_one
      · simp only [hb, ↓reduceIte]
        simp [probEvent_bind_eq_tsum, probEvent_pure, StopOr, hb]
  | query_bind input next ih =>
      cases input with
      | inl draw =>
          rw [risk_private]
          simp only [experiment, run_private]
          rw [probEvent_bind_bind_swap, probEvent_bind_eq_tsum]
          exact ENNReal.tsum_le_tsum fun value => mul_le_mul' le_rfl (ih value known)
      | inr input => cases input with
        | inl coordinate =>
            rw [risk_reveal]
            simp only [experiment, run_reveal]
            rw [probEvent_congr' (fun _ _ => Iff.rfl) (completion_reveal known coordinate
              (fun value table => run table (next value) (known.cacheQuery coordinate value)))]
            rw [probEvent_bind_eq_tsum]
            apply ENNReal.tsum_le_tsum
            rintro ⟨value, known'⟩
            dsimp only
            by_cases hr : (value, known') ∈ support ((randomOracle (spec := ι →ₒ Digest) coordinate).run known)
            · have hc := revealed_cache known coordinate (value, known') hr
              dsimp only at hc
              rw [hc]
              exact mul_le_mul' le_rfl (ih value (known.cacheQuery coordinate value))
            · rw [probOutput_eq_zero_of_not_mem_support hr]
              simp
        | inr guess =>
            rw [risk_guess, experiment]
            simp only [run_guess]
            calc
              _ ≤ (if known guess.1 = none then 1 / (2 : ℝ≥0∞) ^ 128 else 0) +
                  Pr[StopOr bad | experiment (next ()) known] := by
                by_cases hu : known guess.1 = none
                · have hp := completion_guess known guess.1 guess.2 hu
                  simp only [experiment]
                  rw [if_pos hu, ← hp, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
                  rw [probEvent_eq_tsum_ite (completion known) (fun table => table guess.1 = guess.2),
                    ← ENNReal.tsum_add]
                  apply ENNReal.tsum_le_tsum
                  intro table
                  by_cases hh : table guess.1 = guess.2 <;>
                    simp only [hu, hh, true_and, ↓reduceIte] <;> simp [StopOr]
                · simp [hu, experiment]
              _ ≤ _ := add_le_add le_rfl (ih () known)

end LeanSphincs.Security.HiddenReveal

namespace LeanSphincs.Security.HiddenCost
set_option backward.isDefEq.respectTransparency false

/-- Candidate row coupling with both the hidden-input loss and terminal monitors charged to
one and the same actual comparison trace. `bad` may inspect all raw queries and virtual work. -/
theorem common_stop_or_bad_bound {D R A ι α : Type} [Fintype ι]
    (model : HiddenRows.Model D R A ι) (outside : D → R)
    (computation : OracleComp (SourceCostSpec D R ι) α) (known : HiddenReveal.Knowledge ι)
    (bad : α × List (Entry D) → Prop) :
    Pr[HiddenReveal.StopOr bad | HiddenRows.stoppedExperiment model outside (erase (trace computation)) known] ≤
      expectedTraceCharge (comparison model outside computation known) (fun result => result.1.2)
        (rowWeight model) / (2 : ℝ≥0∞) ^ 128 +
      Pr[fun result => bad result.1 | comparison model outside computation known] := by
  rw [HiddenRows.stoppedExperiment_eq]
  refine (HiddenReveal.stop_or_bad_bound _ known bad).trans ?_
  apply add_le_add _ le_rfl
  apply ENNReal.div_le_div_right
  unfold HiddenReveal.expectedGuessCharge expectedTraceCharge
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ support (comparison model outside computation known)
  · exact mul_le_mul' le_rfl (by exact_mod_cast comparison_guess_le_rows model outside computation known result hr)
  · change Pr[= result | comparison model outside computation known] * _ ≤ _
    rw [probOutput_eq_zero_of_not_mem_support hr]
    simp

end LeanSphincs.Security.HiddenCost
