import LeanSphincs.BridgeSmallClose

/-! Real arithmetic for the small-budget bound in closed form: the rates in real form, and one real
inequality on the rates at the right end of the range that gives `q / 2^127`. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal
open HiddenBridge PotentialA

variable [Params]

omit [Params] in
theorem ofReal_natCast_inv {n : ℕ} (hn : 0 < n) : ((n : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((n : ℝ)⁻¹) := by
  rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast hn), ENNReal.ofReal_natCast]

omit [Params] in
theorem contactRate_eq : contactRate = ENNReal.ofReal ((2 : ℝ) ^ 128)⁻¹ := by
  unfold contactRate
  rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

theorem matchRate_eq : matchRate = ENNReal.ofReal (((2 : ℝ) ^ subtreeHeight * 2 ^ 10)⁻¹) := by
  unfold matchRate
  rw [ofReal_natCast_inv (by positivity)]
  push_cast
  norm_num

theorem one_le_keygenCost : 1 ≤ keygenCost := by
  unfold keygenCost
  have : 1 ≤ 2 ^ subtreeHeight := Nat.one_le_two_pow
  omega

omit [Params] in
/-- The real inequality behind the closed form. -/
theorem small_real (x qh q N ρ B c Dx Dh m : ℝ) (hx0 : 0 ≤ x) (hxq : x ≤ qh) (hqh : qh ≤ 2 ^ 127)
    (hq : x + 1 ≤ q) (hN0 : 0 ≤ N) (hN : N ≤ 2 ^ 70) (_hB : 0 ≤ B) (hc : 0 ≤ c) (_hm : 0 ≤ m)
    (hDh : 0 < Dh) (hD : Dh ≤ Dx)
    (hcheck : ρ + 2 ^ 128 * B + N * m + qh / Dh + qh * c + 1 / 2 ^ 60 ≤ 2) :
    ρ * x / 2 ^ 128 + x * B + x * (2 ^ 128)⁻¹ * (N * m + x * Dx⁻¹) + x * (2 ^ 128)⁻¹ * (x * c) +
        ((x + N) + x * (2 ^ 128)⁻¹ * (x + N)) * (1 / 2) ^ 201 + 2 * (q / 2 ^ 256) ≤ q / 2 ^ 127 := by
  have hDx : 0 < Dx := lt_of_lt_of_le hDh hD
  have h1 : x * Dx⁻¹ ≤ qh / Dh := by
    rw [← div_eq_mul_inv]
    exact div_le_div₀ (le_trans hx0 hxq) hxq hDh hD
  have h2 : x * c ≤ qh * c := mul_le_mul_of_nonneg_right hxq hc
  have hbr : ρ + 2 ^ 128 * B + N * m + x * Dx⁻¹ + x * c ≤ 2 - 1 / 2 ^ 60 := by linarith
  have hmain : ρ * x / 2 ^ 128 + x * B + x * (2 ^ 128)⁻¹ * (N * m + x * Dx⁻¹) + x * (2 ^ 128)⁻¹ * (x * c) =
      x * (2 ^ 128)⁻¹ * (ρ + 2 ^ 128 * B + N * m + x * Dx⁻¹ + x * c) := by
    field_simp
    ring
  have hmain' : x * (2 ^ 128)⁻¹ * (ρ + 2 ^ 128 * B + N * m + x * Dx⁻¹ + x * c) ≤
      x * (2 ^ 128)⁻¹ * (2 - 1 / 2 ^ 60) := mul_le_mul_of_nonneg_left hbr (by positivity)
  have hx1 : x * (2 ^ 128 : ℝ)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one (by positivity)]
    linarith
  have hfail : ((x + N) + x * (2 ^ 128)⁻¹ * (x + N)) * (1 / 2) ^ 201 ≤ (x + N) * 2 * (1 / 2) ^ 201 := by
    have : x * (2 ^ 128 : ℝ)⁻¹ * (x + N) ≤ x + N := by
      calc x * (2 ^ 128 : ℝ)⁻¹ * (x + N) ≤ 1 * (x + N) := mul_le_mul_of_nonneg_right hx1 (by positivity)
        _ = x + N := one_mul _
    have hp : (0 : ℝ) ≤ (1 / 2) ^ 201 := by positivity
    nlinarith
  have hq0 : 0 ≤ q := by linarith
  have e201 : ((1 : ℝ) / 2) ^ 201 = 1 / 2 ^ 201 := by rw [div_pow, one_pow]
  rw [hmain]
  rw [e201] at hfail ⊢
  have hxq' : x ≤ 2 ^ 127 := le_trans hxq hqh
  -- everything in units of 2^-255
  have key : x * (2 ^ 128)⁻¹ * (2 - 1 / 2 ^ 60) + (x + N) * 2 * (1 / 2 ^ 201) + 2 * (q / 2 ^ 256) ≤ q / 2 ^ 127 := by
    have ex : x * (2 ^ 128 : ℝ)⁻¹ * (2 - 1 / 2 ^ 60) + (x + N) * 2 * (1 / 2 ^ 201) + 2 * (q / 2 ^ 256) =
        (x * (2 ^ 128 - 2 ^ 67) + (x + N) * 2 ^ 55 + q) / 2 ^ 255 := by
      field_simp
    have ey : q / (2 : ℝ) ^ 127 = q * 2 ^ 128 / 2 ^ 255 := by
      field_simp
    rw [ex, ey]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    linarith
  linarith
