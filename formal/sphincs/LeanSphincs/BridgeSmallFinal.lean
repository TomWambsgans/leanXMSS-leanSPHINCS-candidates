import LeanSphincs.BridgeSmallClose

/-! The small-budget bound in closed form: one real inequality on the rates at the right end of
the range gives `q / 2^127`. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal
open HiddenBridge PotentialA

variable [Params]

theorem ofReal_natCast_inv {n : ℕ} (hn : 0 < n) : ((n : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((n : ℝ)⁻¹) := by
  rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast hn), ENNReal.ofReal_natCast]

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

/-- The real inequality behind the closed form. -/
theorem small_real (x qh q N ρ B c Dx Dh m : ℝ) (hx0 : 0 ≤ x) (hxq : x ≤ qh) (hqh : qh ≤ 2 ^ 127)
    (hq : x + 1 ≤ q) (hN0 : 0 ≤ N) (hN : N ≤ 2 ^ 70) (hB : 0 ≤ B) (hc : 0 ≤ c) (hm : 0 ≤ m)
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **The small-budget bound in closed form.** For every budget whose part after key generation is
at most `qh`, the small-route bound is at most `q / 2^127` once one real inequality holds at `qh`. -/
theorem small_close (q qh : ℕ) (hq1 : 1 ≤ q) (hq' : q - keygenCost ≤ qh) (hqh : qh ≤ 2 ^ 127)
    (hN : signatureLimit ≤ 2 ^ 70) (ρ : ℝ) (hρ : 0 ≤ ρ) (B c : ℚ) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hcheck : ρ + 2 ^ 128 * (B : ℝ) + (signatureLimit : ℝ) * ((2 : ℝ) ^ subtreeHeight * 2 ^ 10)⁻¹ +
        (qh : ℝ) / ((2 ^ 128 - (qh + 2 ^ 32) : ℕ) : ℝ) + qh * (c : ℝ) + 1 / 2 ^ 60 ≤ 2) :
    smallMain ρ q B c + smallFail q * (2 : ℝ≥0∞)⁻¹ ^ 201 + 2 * ((q : ℝ≥0∞) / 2 ^ 256) ≤
      (q : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞) := by
  set q' := q - keygenCost with hq'def
  have hK : 1 ≤ keygenCost := one_le_keygenCost
  have hq'1 : q' + 1 ≤ q := by omega
  have hqh' : qh + 2 ^ 32 < 2 ^ 128 := lt_of_le_of_lt (Nat.add_le_add_right hqh _) (by norm_num)
  have hDh : 0 < 2 ^ 128 - (qh + 2 ^ 32) := Nat.sub_pos_of_lt hqh'
  have hD : 2 ^ 128 - (qh + 2 ^ 32) ≤ 2 ^ 128 - (q' + 2 ^ 32) :=
    Nat.sub_le_sub_left (Nat.add_le_add_right hq' _) _
  have hDq : 0 < 2 ^ 128 - (q' + 2 ^ 32) := lt_of_lt_of_le hDh hD
  have hB' : (0 : ℝ) ≤ B := by exact_mod_cast hB
  have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
  have r1 : (q' : ℝ) ≤ qh := Nat.cast_le.mpr hq'
  have r2 : (qh : ℝ) ≤ 2 ^ 127 := by
    have h := (Nat.cast_le (α := ℝ)).mpr hqh
    rwa [Nat.cast_pow, Nat.cast_ofNat] at h
  have r3 : (q' : ℝ) + 1 ≤ q := by
    have h := (Nat.cast_le (α := ℝ)).mpr hq'1
    rwa [Nat.cast_add, Nat.cast_one] at h
  have r4 : (signatureLimit : ℝ) ≤ 2 ^ 70 := by
    have h := (Nat.cast_le (α := ℝ)).mpr hN
    rwa [Nat.cast_pow, Nat.cast_ofNat] at h
  have r5 : (0 : ℝ) < ((2 ^ 128 - (qh + 2 ^ 32) : ℕ) : ℝ) := Nat.cast_pos.mpr hDh
  have r6 : ((2 ^ 128 - (qh + 2 ^ 32) : ℕ) : ℝ) ≤ ((2 ^ 128 - (q' + 2 ^ 32) : ℕ) : ℝ) := Nat.cast_le.mpr hD
  have hreal := small_real (q' : ℝ) qh q signatureLimit ρ B c ((2 ^ 128 - (q' + 2 ^ 32) : ℕ) : ℝ)
    ((2 ^ 128 - (qh + 2 ^ 32) : ℕ) : ℝ) ((2 : ℝ) ^ subtreeHeight * 2 ^ 10)⁻¹ (Nat.cast_nonneg _)
    r1 r2 r3 (Nat.cast_nonneg _) r4 hB' hc' (by positivity) r5 r6 hcheck
  have hnat : ∀ n : ℕ, (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) := fun n => (ENNReal.ofReal_natCast n).symm
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by rw [ENNReal.ofReal_ofNat]
  have hhalf : (2 : ℝ≥0∞)⁻¹ ^ 201 = ENNReal.ofReal ((1 / 2) ^ 201) := by
    rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  have hq256 : (q : ℝ≥0∞) / 2 ^ 256 = ENNReal.ofReal (q / 2 ^ 256) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_natCast]
  have hq127 : (q : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞) = ENNReal.ofReal (q / 2 ^ 127) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_ofNat]
    push_cast
    norm_num
  have hDinv : (((2 ^ 128 - (q' + 2 ^ 32) : ℕ) : ℝ≥0∞))⁻¹ =
      ENNReal.ofReal ((((2 ^ 128 - (q' + 2 ^ 32) : ℕ) : ℝ))⁻¹) := ofReal_natCast_inv hDq
  unfold smallMain smallFail
  rw [← hq'def, hDinv, hhalf, hq256, hq127, contactRate_eq, matchRate_eq, hnat q', hnat signatureLimit, h2]
  have hD0 : (0 : ℝ) ≤ (((2 ^ 128 - (q' + 2 ^ 32) : ℕ) : ℝ))⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  simp (disch := positivity) only [← ENNReal.ofReal_add, ← ENNReal.ofReal_mul]
  exact ENNReal.ofReal_le_ofReal hreal

