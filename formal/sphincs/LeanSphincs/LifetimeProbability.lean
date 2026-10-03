import LeanSphincs.LifetimeBounds

/-! The probability-valued form of the exact lifetime arithmetic. The recursive binomial
expectation is the generic operator imported from leanVM b7a107256. -/

namespace LeanSphincs.Lifetime

open ENNReal

theorem ofReal_binomialMean {rate : ℝ} (h0 : 0 ≤ rate) (h1 : rate ≤ 1)
    (n : Nat) {f : Nat → ℝ} (hf : ∀ r, 0 ≤ f r) :
    ENNReal.ofReal (binomialMean rate n f) =
      SphincsSecurity.Concrete.binomialAverage (ENNReal.ofReal rate) n
        (fun r => ENNReal.ofReal (f r)) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [binomialMean, SphincsSecurity.Concrete.binomialAverage_succ,
      ENNReal.ofReal_add
        (mul_nonneg (sub_nonneg.mpr h1) (binomialMean_nonneg h0 h1 n hf))
        (mul_nonneg h0 (binomialMean_nonneg h0 h1 n (fun r => hf (r + 1)))),
      ENNReal.ofReal_mul (sub_nonneg.mpr h1), ENNReal.ofReal_mul h0,
      ENNReal.ofReal_sub 1 h0, ENNReal.ofReal_one, ih hf, ih (fun r => hf (r + 1))]

noncomputable def forsBoundENNReal (b n : Nat) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ b / 2 ^ 26 *
    SphincsSecurity.Concrete.binomialAverage ((2 : ℝ≥0∞) ^ b)⁻¹ n
      (fun r => (1 - (1 - (1 : ℝ≥0∞) / 1024) ^ r) ^ 24)

theorem ofReal_forsBound (b n : Nat) :
    ENNReal.ofReal (forsBound b n) = forsBoundENNReal b n := by
  unfold forsBound forsBoundENNReal
  rw [ENNReal.ofReal_mul (by positivity), ofReal_binomialMean (by positivity)
    (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))) n (fun _ => by positivity)]
  simp only [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2 ^ 26),
    ENNReal.ofReal_inv_of_pos (by positivity : (0 : ℝ) < 2 ^ b),
    ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  congr 2
  funext r
  have hhit : (0 : ℝ) ≤ 1 - (1 - 1 / 1024) ^ r :=
    sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num))
  rw [ENNReal.ofReal_pow hhit, ENNReal.ofReal_sub 1 (by positivity),
    ENNReal.ofReal_one, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_sub 1 (by norm_num),
    ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

theorem forsBoundENNReal_le_of_real {b n : Nat}
    (h : forsBound b n ≤ (1 : ℝ) / 2 ^ 127) :
    forsBoundENNReal b n ≤ (1 : ℝ≥0∞) / 2 ^ 127 := by
  rw [← ofReal_forsBound]
  simpa using ENNReal.ofReal_le_ofReal h

theorem fors_lifetime_ennreal_full {n : Nat} (hn : n ≤ 1200000000) :
    forsBoundENNReal 26 n ≤ (1 : ℝ≥0∞) / 2 ^ 127 :=
  forsBoundENNReal_le_of_real (fors_lifetime_full_le hn)

theorem fors_lifetime_ennreal_pruned20 {n : Nat} (hn : n ≤ 23700000) :
    forsBoundENNReal 20 n ≤ (1 : ℝ≥0∞) / 2 ^ 127 :=
  forsBoundENNReal_le_of_real (fors_lifetime_pruned20_le hn)

theorem fors_lifetime_ennreal_pruned13 {n : Nat} (hn : n ≤ 240000) :
    forsBoundENNReal 13 n ≤ (1 : ℝ≥0∞) / 2 ^ 127 :=
  forsBoundENNReal_le_of_real (fors_lifetime_pruned13_le hn)

theorem fors_lifetime_ennreal_pruned14 {n : Nat} (hn : n ≤ 460000) :
    forsBoundENNReal 14 n ≤ (1 : ℝ≥0∞) / 2 ^ 127 :=
  forsBoundENNReal_le_of_real (fors_lifetime_pruned14_le hn)

theorem fors_lifetime_ennreal_pruned12 {n : Nat} (hn : n ≤ 125000) :
    forsBoundENNReal 12 n ≤ (1 : ℝ≥0∞) / 2 ^ 127 :=
  forsBoundENNReal_le_of_real (fors_lifetime_pruned12_le hn)

theorem fors_lifetime_ennreal_pruned10 {n : Nat} (hn : n ≤ 33) :
    forsBoundENNReal 10 n ≤ (1 : ℝ≥0∞) / 2 ^ 127 :=
  forsBoundENNReal_le_of_real (fors_lifetime_pruned10_le hn)

end LeanSphincs.Lifetime
