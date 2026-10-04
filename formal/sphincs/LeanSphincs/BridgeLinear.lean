import LeanSphincs.BridgeInterp

/-! A linear potential on the interpreted comparison. If a potential of the remaining budget and
the state bounds the expected final payoff of every state, and every step keeps its expectation,
paying a fixed amount per message-digest query, then the potential at the start bounds the
expected final payoff plus the payments of the whole run. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.HiddenDebt

open HiddenCost HiddenBridge HiddenOutside HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
variable (tg : Targeting D R ι) (initial : Cache D R) (model : HiddenRows.Model D R A ι)

/-- Number of message-digest queries of a trace. -/
noncomputable def digestCount (entries : List (Entry D)) : ℕ :=
  (entries.filter fun entry => match entry with
    | .inl input => decide (tg.digest input)
    | .inr _ => false).length

omit [Fintype ι] [SampleableType R] in
theorem digestCount_append (first second : List (Entry D)) :
    digestCount tg (first ++ second) = digestCount tg first + digestCount tg second := by
  simp [digestCount, List.filter_append]

/-- Expected final payoff of a state, once its unexposed coordinates are completed. -/
noncomputable def endValue (payoff : (ι → Digest) → DebtState D R ι → ℝ≥0∞) (state : DebtState D R ι) :
    ℝ≥0∞ :=
  ∑' table, Pr[= table | completion state.known] * payoff table state

/-- **Linear potential on the interpreter.** -/
theorem interp_potential {α : Type} (Inv : DebtState D R ι → Prop) (Φ : ℕ → DebtState D R ι → ℝ≥0∞)
    (payoff : (ι → Digest) → DebtState D R ι → ℝ≥0∞) (pay : ℝ≥0∞)
    (hfinal : ∀ budget state, Inv state → endValue payoff state ≤ Φ budget state)
    (hstep : ∀ (input : (SourceCostSpec D R ι).Domain) budget state, Inv state → sourceCost input ≤ budget →
      ∑' result, Pr[= result | costStep model input state] * Φ (budget - sourceCost input) result.2 +
        pay * digestCount tg (recorded input) ≤ Φ budget state)
    (hinv : ∀ input state, Inv state → ∀ result ∈ support (costStep model input state), Inv result.2)
    (computation : OracleComp (SourceCostSpec D R ι) α) :
    ∀ budget state, Inv state →
      ∑' out, Pr[= out | interp tg initial model computation budget state] *
        (endValue payoff out.2 + pay * digestCount tg out.1.2.2.1) ≤ Φ budget state := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro budget state hstate
      rw [interp_pure, tsum_probOutput_pure_mul]
      simpa [digestCount] using hfinal budget state hstate
  | query_bind input next ih =>
      intro budget state hstate
      rw [interp_query_bind]
      split_ifs with hcost
      · rw [tsum_probOutput_bind_mul]
        calc ∑' result, Pr[= result | costStep model input state] *
              ∑' out, Pr[= out | (fun out => ((out.1.1, revealed input ++ out.1.2.1,
                  recorded input ++ out.1.2.2.1, touch tg initial state input ++ out.1.2.2.2), out.2)) <$>
                interp tg initial model (next result.1) (budget - sourceCost input) result.2] *
                (endValue payoff out.2 + pay * digestCount tg out.1.2.2.1)
            ≤ ∑' result, Pr[= result | costStep model input state] *
                (Φ (budget - sourceCost input) result.2 + pay * digestCount tg (recorded input)) := by
              refine ENNReal.tsum_le_tsum fun result => ?_
              by_cases hr : result ∈ support (costStep model input state)
              · refine mul_le_mul_right ?_ _
                rw [tsum_probOutput_map_mul]
                simp only [digestCount_append, Nat.cast_add]
                calc ∑' out, Pr[= out | interp tg initial model (next result.1) (budget - sourceCost input) result.2] *
                      (endValue payoff out.2 + pay * ((digestCount tg (recorded input) : ℝ≥0∞) +
                        digestCount tg out.1.2.2.1))
                    = ∑' out, Pr[= out | interp tg initial model (next result.1) (budget - sourceCost input) result.2] *
                        (endValue payoff out.2 + pay * digestCount tg out.1.2.2.1) +
                      (∑' out, Pr[= out | interp tg initial model (next result.1)
                        (budget - sourceCost input) result.2]) * (pay * digestCount tg (recorded input)) := by
                      rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
                      refine tsum_congr fun out => ?_
                      ring
                  _ ≤ Φ (budget - sourceCost input) result.2 + 1 * (pay * digestCount tg (recorded input)) :=
                      add_le_add (ih result.1 _ _ (hinv input state hstate result hr))
                        (mul_le_mul' tsum_probOutput_le_one le_rfl)
                  _ = _ := by rw [one_mul]
              · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
          _ = ∑' result, Pr[= result | costStep model input state] * Φ (budget - sourceCost input) result.2 +
                (∑' result, Pr[= result | costStep model input state]) * (pay * digestCount tg (recorded input)) := by
              rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
              refine tsum_congr fun result => ?_
              ring
          _ ≤ ∑' result, Pr[= result | costStep model input state] * Φ (budget - sourceCost input) result.2 +
                1 * (pay * digestCount tg (recorded input)) :=
              add_le_add le_rfl (mul_le_mul' tsum_probOutput_le_one le_rfl)
          _ ≤ _ := by rw [one_mul]; exact hstep input budget state hstate hcost
      · rw [tsum_probOutput_pure_mul]
        simpa [digestCount] using hfinal budget state hstate

end LeanSphincs.Security.HiddenDebt
