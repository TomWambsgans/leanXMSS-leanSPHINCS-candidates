import LeanSphincs.BridgeContactSample

/-! The fair share `wbarOf y` of the budget `y = q - keygenCost`, as used by the A4 bounds: its
near forecast is the near H-term, it is fair for the signer's attempts, and its product with
`landing`. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

/-- The near forecast at the fair share is the near H-term. -/
theorem startNear_wbarOf (q : ℕ) : startNear (H0.wbarOf q) q = H0.hNearOf q := rfl

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
