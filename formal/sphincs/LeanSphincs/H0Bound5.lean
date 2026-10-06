import LeanSphincs.H0BoundOnce
import LeanSphincs.BridgeStateFn

/-! The coin of a future digest pair under the signer that tries `R0, R0 + 1, ...`:
`wbar5 = (2 - landing) / (2^128 · landing)`, independent of the budget. A digest query adds at most
`rate5 = (2 - landing) / 2^128` selection mass (`Walk.grp_step`), and the selection probabilities of
the walk are exact, so the budget-dependent share `wbarOf q` of the per-attempt signer is not
needed. -/

open ENNReal

namespace LeanSphincs.Security.H0

open Concrete Domination ForsPrice ForsPotential

set_option linter.unusedSectionVars false
set_option exponentiation.threshold 512

variable [Params]

/-- Coin probability of a future digest pair. -/
noncomputable def wbar5 : ℝ≥0∞ := rate5 / landing

theorem landing_ne_top : landing ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top landing_le_one

theorem wbar5_mul_landing : wbar5 * landing = rate5 := by
  unfold wbar5
  exact ENNReal.div_mul_cancel landing_ne_zero landing_ne_top

theorem rate5_eq : rate5 = ENNReal.ofReal ((2 - 1 / 2 ^ (26 - subtreeHeight)) / 2 ^ 128) := by
  unfold rate5
  rw [GraphView.card_randomness, landing_eq]
  have h1 : (1 : ℝ) / 2 ^ (26 - subtreeHeight) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  have h2 : (0 : ℝ) ≤ 1 / 2 ^ (26 - subtreeHeight) := by positivity
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ h2, ← ENNReal.ofReal_add zero_le_one (by linarith),
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos (by positivity),
    ← ENNReal.ofReal_mul (by linarith)]
  congr 1
  push_cast
  ring

theorem wbar5_eq : wbar5 = ENNReal.ofReal ((2 * 2 ^ (26 - subtreeHeight) - 1) / 2 ^ 128) := by
  unfold wbar5
  rw [rate5_eq, landing_eq, ← ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  field_simp

theorem wbar5_le_one : wbar5 ≤ 1 := by
  rw [wbar5_eq, ← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_one (by positivity)]
  have h26 : (2 : ℝ) ^ (26 - subtreeHeight) ≤ 2 ^ 26 := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have : (2 : ℝ) * 2 ^ 26 ≤ 2 ^ 128 := by norm_num
  linarith

/-- **The coin pays the rate of the walk.** -/
theorem fair5 : Fair5 wbar5 where
  ne_top := ne_top_of_le_ne_top ENNReal.one_ne_top wbar5_le_one
  le_one := wbar5_le_one
  rate := by rw [mul_comm, wbar5_mul_landing]

/-! ### The rational rate bound for the coin of the walk -/

/-- Upper bound for the one-coin Poisson rate with the coin `wbar5` at the right end `qb` of an
interval: `landing * wbar5 = (2 - 2^-(26-b)) / 2^128` and `wbar5 * 2^b = (2^27 - 2^b) / 2^128`. -/
def muOnceQ5 (b N qb R : ℕ) : ℚ :=
  (N : ℚ) / 2 ^ b +
    ((qb : ℚ) * (2 - 1 / 2 ^ (26 - b)) / 2 ^ 128) * (1 + (2 ^ 27 - 2 ^ b) / (2 : ℚ) ^ 128) ^ (24 * R) / 2 ^ b

/-- The one-coin Poisson rate with the coin `wbar5`, in real form, is below the certificate bound. -/
theorem mu_leO5 (b N R q qb : ℕ) (hb : subtreeHeight = b) (hq : q ≤ qb) (μh : ℝ)
    (hμ : (muOnceQ5 b N qb R : ℝ) ≤ μh) :
    (N : ℝ≥0∞) * ((Fintype.card (Fin (2 ^ subtreeHeight)) : ℕ) : ℝ≥0∞)⁻¹ +
      (q : ℝ≥0∞) * (landing * wbar5 *
        (1 + wbar5 * ((Fintype.card (Fin (2 ^ subtreeHeight)) : ℕ) : ℝ≥0∞)) ^ (24 * R) /
          ((Fintype.card (Fin (2 ^ subtreeHeight)) : ℕ) : ℝ≥0∞)) ≤ ENNReal.ofReal μh := by
  have hb26 : b ≤ 26 := hb ▸ subtree_le_26
  have hpow1 : (1 : ℝ) ≤ 2 ^ (26 - b) := one_le_pow₀ (by norm_num)
  obtain ⟨wr, hwr, hw0⟩ : ∃ wr : ℝ, wr = (2 * 2 ^ (26 - b) - 1) / 2 ^ 128 ∧ 0 ≤ wr :=
    ⟨_, rfl, div_nonneg (by linarith) (by positivity)⟩
  have hA : (1 : ℝ) / 2 ^ (26 - b) * wr = (2 - 1 / 2 ^ (26 - b)) / 2 ^ 128 := by
    rw [hwr]; field_simp
  have hM : (2 : ℝ) ^ (26 - b) * 2 ^ b = 2 ^ 26 := by rw [← pow_add, Nat.sub_add_cancel hb26]
  have hB : wr * 2 ^ b = ((2 : ℝ) ^ 27 - 2 ^ b) / 2 ^ 128 := by
    rw [hwr, div_mul_eq_mul_div]
    congr 1
    linear_combination 2 * hM
  have hA0 : (0 : ℝ) ≤ (2 - 1 / 2 ^ (26 - b)) / 2 ^ 128 := by rw [← hA]; positivity
  have hB0 : (0 : ℝ) ≤ ((2 : ℝ) ^ 27 - 2 ^ b) / 2 ^ 128 := by rw [← hB]; positivity
  rw [wbar5_eq, landing_eq, card_eq, hb, ← hwr, ← ENNReal.ofReal_natCast N, ← ENNReal.ofReal_natCast q,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_inv_of_pos (by positivity)]
  simp (disch := positivity) only [← ENNReal.ofReal_mul, ← ENNReal.ofReal_add, ← ENNReal.ofReal_pow,
    ← ENNReal.ofReal_div_of_pos]
  apply ENNReal.ofReal_le_ofReal
  refine le_trans ?_ hμ
  have hform : (N : ℝ) * (2 ^ b)⁻¹ + q * (1 / 2 ^ (26 - b) * wr * (1 + wr * 2 ^ b) ^ (24 * R) / 2 ^ b) =
      (N : ℝ) / 2 ^ b + ((q : ℝ) * ((2 - 1 / 2 ^ (26 - b)) / 2 ^ 128)) *
        (1 + ((2 : ℝ) ^ 27 - 2 ^ b) / 2 ^ 128) ^ (24 * R) / 2 ^ b := by
    rw [← hA, ← hB]; ring
  rw [hform]
  unfold muOnceQ5
  push_cast
  have hqq : (q : ℝ) ≤ qb := by exact_mod_cast hq
  rw [mul_div_assoc (qb : ℝ)]
  gcongr

end LeanSphincs.Security.H0
