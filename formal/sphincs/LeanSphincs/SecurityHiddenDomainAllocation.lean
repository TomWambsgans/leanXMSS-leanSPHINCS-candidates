import LeanSphincs.SecurityHiddenAccounting
import LeanSphincs.SecurityHiddenGraph

/-! Exact seed/row domain separation and finite-monitor allocation on the common trace. -/

open OracleComp OracleSpec ENNReal
namespace LeanSphincs.Security.HiddenCost
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 100000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] HiddenGraph.parse HiddenGraph.input Prefix.combine

/-- Each raw row input is a verifier hash input and therefore cannot also name a master seed. -/
theorem graph_row_seed_disjoint (parameter : PublicParameter) (active : HiddenGraph.Address → Prop)
    (high : HiddenGraph.Address → Prefix.High) (input : HashInput)
    (hrow : ((HiddenGraph.rowModel parameter active high).parse input).isSome = true) :
    SeedGuess.parseSeed input = none := by
  change (HiddenGraph.parse parameter active input).isSome = true at hrow
  cases hp : HiddenGraph.parse parameter active input with
  | none => simp [hp] at hrow
  | some query =>
      obtain ⟨rfl, _⟩ := (HiddenGraph.parse_some_iff parameter active input query).mp hp
      simpa only [HiddenGraph.input] using
        SeedGuess.parseSeed_verifier parameter query.1.position.domain (bytesLE 16 query.2)

theorem seed_row_entry_le (parameter : PublicParameter) (active : HiddenGraph.Address → Prop)
    (high : HiddenGraph.Address → Prefix.High) (entry : Entry HashInput) :
    seedWeight entry + rowWeight (HiddenGraph.rowModel parameter active high) entry ≤ entryCost entry := by
  cases entry with
  | inr amount => simp [seedWeight, rowWeight, entryCost]
  | inl input =>
      by_cases hrow : ((HiddenGraph.rowModel parameter active high).parse input).isSome = true
      · have hs := graph_row_seed_disjoint parameter active high input hrow
        simp [seedWeight, rowWeight, hrow, hs, entryCost]
      · simp only [seedWeight, rowWeight, entryCost]
        split_ifs <;> simp_all

/-- Local domain counts, including the seed monitor and hidden-row monitor, share the original
budget on the very comparison whose seed and hidden-input losses were proved. -/
theorem capped_seed_row_allocation {α : Type} (parameter : PublicParameter)
    (active : HiddenGraph.Address → Prop) (high : HiddenGraph.Address → Prefix.High)
    (outside : HashInput → HashOutput)
    (computation : OracleComp (SourceCostSpec HashInput HashOutput HiddenGraph.Coordinate) α)
    (known : HiddenGraph.Knowledge) (budget : Nat) :
    expectedTraceCharge (comparison (HiddenGraph.rowModel parameter active high) outside
        (cap computation budget) known) (fun result => result.1.2) seedWeight +
      expectedTraceCharge (comparison (HiddenGraph.rowModel parameter active high) outside
        (cap computation budget) known) (fun result => result.1.2)
        (rowWeight (HiddenGraph.rowModel parameter active high)) ≤ budget :=
  expectedTraceCharge_add_le _ _ _ _ (seed_row_entry_le parameter active high) budget
    (capped_comparison_cost_le _ outside computation known budget)

/-- Per-entry rates compose before expectation. This permits input and output monitors to
share a row's two-digest allowance while seed, message, and encoding domains consume their
own disjoint entries; virtual honest work remains included in the total budget. -/
theorem trace_rate_allocation {D κ : Type} [Fintype κ]
    (weights : κ → Entry D → Nat) (rates : κ → ℝ≥0∞) (allowance : ℝ≥0∞)
    (hlocal : ∀ entry, (∑ monitor, (weights monitor entry : ℝ≥0∞) * rates monitor) ≤
      (entryCost entry : ℝ≥0∞) * allowance) (entries : List (Entry D)) :
    (∑ monitor, (traceCharge (weights monitor) entries : ℝ≥0∞) * rates monitor) ≤
      (traceCost entries : ℝ≥0∞) * allowance := by
  induction entries with
  | nil => simp [traceCharge, traceCost]
  | cons entry entries ih =>
      simp only [traceCharge, traceCost, List.map_cons, List.sum_cons, Nat.cast_add,
        add_mul, Finset.sum_add_distrib] at ih ⊢
      exact add_le_add (hlocal entry) ih

theorem expected_rate_allocation {D Ω κ : Type} [Fintype κ] (program : ProbComp Ω)
    (entries : Ω → List (Entry D)) (weights : κ → Entry D → Nat) (rates : κ → ℝ≥0∞)
    (allowance : ℝ≥0∞)
    (hlocal : ∀ entry, (∑ monitor, (weights monitor entry : ℝ≥0∞) * rates monitor) ≤
      (entryCost entry : ℝ≥0∞) * allowance)
    (budget : Nat) (hbudget : ∀ result ∈ support program, traceCost (entries result) ≤ budget) :
    (∑ monitor, expectedTraceCharge program entries (weights monitor) * rates monitor) ≤
      (budget : ℝ≥0∞) * allowance := by
  simp only [expectedTraceCharge, ← ENNReal.tsum_mul_right, mul_assoc]
  have hswap := ENNReal.tsum_comm (f := fun monitor : κ => fun result : Ω =>
    Pr[= result | program] * ((traceCharge (weights monitor) (entries result) : ℝ≥0∞) * rates monitor))
  simp only [tsum_fintype] at hswap
  rw [hswap]
  calc
    _ ≤ ∑' result, Pr[= result | program] * ((budget : ℝ≥0∞) * allowance) := by
      apply ENNReal.tsum_le_tsum
      intro result
      rw [← Finset.mul_sum]
      by_cases hr : result ∈ support program
      · apply mul_le_mul' le_rfl
        exact (trace_rate_allocation weights rates allowance hlocal (entries result)).trans
          (mul_le_mul' (by exact_mod_cast hbudget result hr) le_rfl)
      · rw [probOutput_eq_zero_of_not_mem_support hr]
        simp
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left zero_le tsum_probOutput_le_one

theorem capped_rate_allocation {D R A ι α κ : Type} [Fintype ι] [Fintype κ]
    (model : HiddenRows.Model D R A ι) (outside : D → R)
    (computation : OracleComp (SourceCostSpec D R ι) α) (known : HiddenReveal.Knowledge ι)
    (weights : κ → Entry D → Nat) (rates : κ → ℝ≥0∞) (allowance : ℝ≥0∞)
    (hlocal : ∀ entry, (∑ monitor, (weights monitor entry : ℝ≥0∞) * rates monitor) ≤
      (entryCost entry : ℝ≥0∞) * allowance) (budget : Nat) :
    (∑ monitor, expectedTraceCharge (comparison model outside (cap computation budget) known)
      (fun result => result.1.2) (weights monitor) * rates monitor) ≤
      (budget : ℝ≥0∞) * allowance :=
  expected_rate_allocation _ _ weights rates allowance hlocal budget
    (capped_comparison_cost_le model outside computation known budget)

end LeanSphincs.Security.HiddenCost
