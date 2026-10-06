import LeanSphincs.BridgeContactSample

/-! The coin `wbar5` of the signer that tries `R0, R0 + 1, ...`, as used by the A4 bounds: its near
forecast is the near H-term and it pays the rate of the walk (`Fair5`); its product with `landing`
is `rate5` (`H0.wbar5_mul_landing`, `H0.rate5_eq`). The fair share `wbarOf y` of the per-attempt
signer is kept for the frozen modules: it is fair for the signer's attempts, and its product with
`landing`. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

/-- The near forecast at the coin of the walk is the near H-term. -/
theorem startNear_wbar5 (q : ℕ) : startNear H0.wbar5 q = H0.hNearOf q := rfl

/-- The coin of the walk pays its rate. -/
theorem fair_wbar5 : Fair5 H0.wbar5 := H0.fair5

/-- The fair share is fair for the signer's attempts. -/
theorem fair_wbarOf (y : ℕ) (hy : 2 * y ≤ 2 ^ 128) : Fair (H0.wbarOf y) (y + digestAttemptLimit) :=
  H0.fair_of y hy

theorem wbarOf_mul_landing (y : ℕ) : H0.wbarOf y * landing = (((2 ^ 128 - (y + 2 ^ 32) : ℕ) : ℝ≥0∞))⁻¹ := by
  have hland0 : landing ≠ 0 := by
    unfold landing
    exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)
  have hlandT : landing ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top landing_le_one
  unfold H0.wbarOf
  rw [ENNReal.mul_inv (Or.inr hlandT) (Or.inr hland0), mul_assoc, ENNReal.inv_mul_cancel hland0 hlandT, mul_one]

end LeanSphincs.Security.ForsPotential
