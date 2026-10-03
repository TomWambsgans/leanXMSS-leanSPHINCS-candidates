import LeanSphincs.LifetimeMoments

/-!
Exact, kernel-checked FORS bounds for the six requested lifetimes. The bound is the binomial
occupancy expression used by `scripts/fors_security.py`, multiplied by the pruned-subtree
landing probability. This file proves the arithmetic; it does not assert that the adaptive
SUF-CMA game has already been reduced to that expression.
-/

namespace LeanSphincs.Lifetime

set_option exponentiation.threshold 1024

/-- Fresh-digest FORS coverage averaged over independent signatures in the kept subtree. -/
noncomputable def forsBound (b n : Nat) : ℝ :=
  (2 : ℝ) ^ b / 2 ^ 26 * binomialMean ((2 : ℝ) ^ b)⁻¹ n
    (fun r => (1 - (1 - (1 : ℝ) / 1024) ^ r) ^ 24)

theorem forsBound_nonneg (b n : Nat) : 0 ≤ forsBound b n := by
  apply mul_nonneg (by positivity)
  apply binomialMean_nonneg (by positivity)
    (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
  intro r
  positivity

theorem forsBound_mono (b : Nat) : Monotone (forsBound b) := by
  intro n m hnm
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply binomialMean_mono_steps (by positivity)
    (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))) _ hnm
  intro i j hij
  apply pow_le_pow_left₀
  · apply sub_nonneg.mpr
    exact pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 - 1 / 1024) (by norm_num)
  · apply sub_le_sub_left
    exact pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 - 1 / 1024)
      (by norm_num) hij

/-- An integer-only certificate for the degree-26 moment bound. -/
def Certificate (b n : Nat) : Prop :=
  1060941 * (2 ^ b) ^ 2 * momentNumerator b n 24 + 73 * momentNumerator b n 26 ≤
    12438 * (2 ^ b) * momentNumerator b n 25 + 2 ^ 159 * (2 ^ b) ^ 25

theorem forsBound_le_of_certificate (b n : Nat) (h : Certificate b n) :
    forsBound b n ≤ (1 : ℝ) / 2 ^ 127 := by
  have hB : (0 : ℝ) < 2 ^ b := by positivity
  have hrate : (2 ^ b : ℝ)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    exact one_le_pow₀ (by norm_num)
  have hm := binomialMean_fors_le (inv_nonneg.mpr hB.le) hrate
    (by norm_num : (0 : ℝ) ≤ 1 / 1024) (by norm_num : (1 : ℝ) / 1024 ≤ 1) n
  rw [binomialMean_power_numerator, binomialMean_power_numerator,
    binomialMean_power_numerator] at hm
  have hcast : (1060941 : ℝ) * (2 ^ b) ^ 2 * momentNumerator b n 24 +
      73 * momentNumerator b n 26 ≤ 12438 * (2 ^ b) * momentNumerator b n 25 +
      2 ^ 159 * (2 ^ b) ^ 25 := by
    exact_mod_cast h
  unfold forsBound
  apply (mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ 2 ^ b / 2 ^ 26)).trans
  have heq : (2 : ℝ) ^ b / 2 ^ 26 * ((1 / 1024 : ℝ) ^ 24 *
      ((1 + 12 * (1 / 1024) + 77 * (1 / 1024) ^ 2) *
          (momentNumerator b n 24 / ((2 : ℝ) ^ b) ^ 24) -
        (12 * (1 / 1024) + 150 * (1 / 1024) ^ 2) *
          (momentNumerator b n 25 / ((2 : ℝ) ^ b) ^ 25) +
        73 * (1 / 1024) ^ 2 * (momentNumerator b n 26 / ((2 : ℝ) ^ b) ^ 26))) =
      (1060941 * (2 ^ b) ^ 2 * momentNumerator b n 24 + 73 * momentNumerator b n 26 -
        12438 * (2 ^ b) * momentNumerator b n 25) / (2 ^ 286 * (2 ^ b) ^ 25) := by
    field_simp
    ring
  rw [heq]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ 286 * (2 ^ b) ^ 25)).2
  have hid : (1 : ℝ) / 2 ^ 127 * (2 ^ 286 * (2 ^ b) ^ 25) =
      2 ^ 159 * (2 ^ b) ^ 25 := by ring
  rw [hid]
  linarith only [hcast]

set_option maxHeartbeats 5000000 in
theorem certificate_full : Certificate 26 1200000000 := by
  norm_num [Certificate, momentNumerator, Finset.sum_range_succ,
    Nat.stirlingSecond, Nat.descFactorial]

set_option maxHeartbeats 5000000 in
theorem certificate_pruned20 : Certificate 20 23700000 := by
  norm_num [Certificate, momentNumerator, Finset.sum_range_succ,
    Nat.stirlingSecond, Nat.descFactorial]

set_option maxHeartbeats 5000000 in
theorem certificate_pruned13 : Certificate 13 240000 := by
  norm_num [Certificate, momentNumerator, Finset.sum_range_succ,
    Nat.stirlingSecond, Nat.descFactorial]

set_option maxHeartbeats 5000000 in
theorem certificate_pruned14 : Certificate 14 460000 := by
  norm_num [Certificate, momentNumerator, Finset.sum_range_succ,
    Nat.stirlingSecond, Nat.descFactorial]

set_option maxHeartbeats 5000000 in
theorem certificate_pruned12 : Certificate 12 125000 := by
  norm_num [Certificate, momentNumerator, Finset.sum_range_succ,
    Nat.stirlingSecond, Nat.descFactorial]

set_option maxHeartbeats 5000000 in
theorem certificate_pruned10 : Certificate 10 33 := by
  norm_num [Certificate, momentNumerator, Finset.sum_range_succ,
    Nat.stirlingSecond, Nat.descFactorial]

theorem fors_lifetime_full : forsBound 26 1200000000 ≤ (1 : ℝ) / 2 ^ 127 :=
  forsBound_le_of_certificate _ _ certificate_full

theorem fors_lifetime_pruned20 : forsBound 20 23700000 ≤ (1 : ℝ) / 2 ^ 127 :=
  forsBound_le_of_certificate _ _ certificate_pruned20

theorem fors_lifetime_pruned13 : forsBound 13 240000 ≤ (1 : ℝ) / 2 ^ 127 :=
  forsBound_le_of_certificate _ _ certificate_pruned13

theorem fors_lifetime_pruned14 : forsBound 14 460000 ≤ (1 : ℝ) / 2 ^ 127 :=
  forsBound_le_of_certificate _ _ certificate_pruned14

theorem fors_lifetime_pruned12 : forsBound 12 125000 ≤ (1 : ℝ) / 2 ^ 127 :=
  forsBound_le_of_certificate _ _ certificate_pruned12

theorem fors_lifetime_pruned10 : forsBound 10 33 ≤ (1 : ℝ) / 2 ^ 127 :=
  forsBound_le_of_certificate _ _ certificate_pruned10

theorem fors_lifetime_full_le {n : Nat} (hn : n ≤ 1200000000) :
    forsBound 26 n ≤ (1 : ℝ) / 2 ^ 127 :=
  (forsBound_mono _ hn).trans fors_lifetime_full

theorem fors_lifetime_pruned20_le {n : Nat} (hn : n ≤ 23700000) :
    forsBound 20 n ≤ (1 : ℝ) / 2 ^ 127 :=
  (forsBound_mono _ hn).trans fors_lifetime_pruned20

theorem fors_lifetime_pruned13_le {n : Nat} (hn : n ≤ 240000) :
    forsBound 13 n ≤ (1 : ℝ) / 2 ^ 127 :=
  (forsBound_mono _ hn).trans fors_lifetime_pruned13

theorem fors_lifetime_pruned14_le {n : Nat} (hn : n ≤ 460000) :
    forsBound 14 n ≤ (1 : ℝ) / 2 ^ 127 :=
  (forsBound_mono _ hn).trans fors_lifetime_pruned14

theorem fors_lifetime_pruned12_le {n : Nat} (hn : n ≤ 125000) :
    forsBound 12 n ≤ (1 : ℝ) / 2 ^ 127 :=
  (forsBound_mono _ hn).trans fors_lifetime_pruned12

theorem fors_lifetime_pruned10_le {n : Nat} (hn : n ≤ 33) :
    forsBound 10 n ≤ (1 : ℝ) / 2 ^ 127 :=
  (forsBound_mono _ hn).trans fors_lifetime_pruned10

end LeanSphincs.Lifetime
