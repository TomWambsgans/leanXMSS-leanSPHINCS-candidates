import FORS.LazyRun.Saturation

/-! **The remaining-budget weight with a real exponent** (survival-weighted route).
`budgetE e p r = ((N - p - r) / (N - p))^e` with a real exponent `e`; `budget` is the case `e = 2`.
The survival-weighted route runs the budget at the exponent `ρ` while nothing is armed, at `2` once
armed, and higher after contacts. This file holds the budget, its probe step, its digest decrement,
and the real inequalities behind the exponent jumps. -/

open ENNReal

namespace FORS.Security.HiddenDebt

variable [Params]

set_option linter.unusedSectionVars false

/-- Remaining-budget weight with a real exponent `e`: `((N - p - r) / (N - p))^e`. -/
noncomputable def budgetE (e : ℝ) (probes remaining : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (((spaceReal - probes - remaining) / (spaceReal - probes)) ^ e)

/-- The second-order upper bound of `1 - (1 - x)^ρ` for `1 ≤ ρ ≤ 2`. -/
noncomputable def satUp (ρ x : ℝ) : ℝ := ρ * x - ρ * (ρ - 1) * x ^ 2 / 2

/-- **`1 - (1 - x)^ρ ≤ ρ x - ρ (ρ - 1) x² / 2`** for `0 ≤ x ≤ 1`, `1 ≤ ρ ≤ 2`: the third derivative
of `(1 - x)^ρ` is nonnegative. -/
theorem one_sub_rpow_le_satUp {ρ x : ℝ} (hρ1 : 1 ≤ ρ) (hρ2 : ρ ≤ 2) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1 - (1 - x) ^ ρ ≤ satUp ρ x := by
  sorry

/-- The start of the route: `1 - budgetE ρ 0 q ≤ satUp ρ (q / 2^128)`. -/
theorem one_sub_budgetE_start_le {ρ : ℝ} (hρ1 : 1 ≤ ρ) (hρ2 : ρ ≤ 2) (q : ℕ) (hq : (q : ℝ) ≤ spaceReal) :
    1 - budgetE ρ 0 q ≤ ENNReal.ofReal (satUp ρ ((q : ℝ) / 2 ^ 128)) := by
  sorry

end FORS.Security.HiddenDebt
