import LeanSphincs.LifetimeVarianceBudget

/-! Exact reserve for the adaptive lifetime correction. The arithmetic closes a normalized
self-bounding inequality; the actual security game must still be shown to satisfy it. -/

namespace LeanSphincs.Lifetime
set_option exponentiation.threshold 1024

def ReserveCertificate (b n : Nat) : Prop :=
  64 * (1060941 * (2 ^ b) ^ 2 * momentNumerator b n 24 + 73 * momentNumerator b n 26) ≤
    64 * 12438 * (2 ^ b) * momentNumerator b n 25 + 63 * 2 ^ 159 * (2 ^ b) ^ 25

theorem forsBound_le_of_reserveCertificate (b n : Nat) (h : ReserveCertificate b n) :
    forsBound b n ≤ (63 : ℝ) / 64 / 2 ^ 127 := by
  have hB : (0 : ℝ) < 2 ^ b := by positivity
  have hrate : (2 ^ b : ℝ)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    exact one_le_pow₀ (by norm_num)
  have hm := binomialMean_fors_le (inv_nonneg.mpr hB.le) hrate
    (by norm_num : (0 : ℝ) ≤ 1 / 1024) (by norm_num : (1 : ℝ) / 1024 ≤ 1) n
  rw [binomialMean_power_numerator, binomialMean_power_numerator,
    binomialMean_power_numerator] at hm
  have hcast : 64 * ((1060941 : ℝ) * (2 ^ b) ^ 2 * momentNumerator b n 24 +
      73 * momentNumerator b n 26) ≤ 64 * 12438 * (2 ^ b) * momentNumerator b n 25 +
      63 * 2 ^ 159 * (2 ^ b) ^ 25 := by
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
  have hid : (63 : ℝ) / 64 / 2 ^ 127 * (2 ^ 286 * (2 ^ b) ^ 25) =
      (63 / 64) * 2 ^ 159 * (2 ^ b) ^ 25 := by ring
  rw [hid]
  linarith only [hcast]

set_option maxHeartbeats 5000000 in
theorem reserveCertificate_full : ReserveCertificate 26 1200000000 := by
  norm_num [ReserveCertificate, momentNumerator, Finset.sum_range_succ,
    Nat.stirlingSecond, Nat.descFactorial]

set_option maxHeartbeats 5000000 in
theorem reserveCertificate_pruned20 : ReserveCertificate 20 23700000 := by
  norm_num [ReserveCertificate, momentNumerator, Finset.sum_range_succ,
    Nat.stirlingSecond, Nat.descFactorial]

set_option maxHeartbeats 5000000 in
theorem reserveCertificate_pruned13 : ReserveCertificate 13 240000 := by
  norm_num [ReserveCertificate, momentNumerator, Finset.sum_range_succ,
    Nat.stirlingSecond, Nat.descFactorial]

set_option maxHeartbeats 5000000 in
theorem reserveCertificate_pruned14 : ReserveCertificate 14 460000 := by
  norm_num [ReserveCertificate, momentNumerator, Finset.sum_range_succ,
    Nat.stirlingSecond, Nat.descFactorial]

set_option maxHeartbeats 5000000 in
theorem reserveCertificate_pruned12 : ReserveCertificate 12 125000 := by
  norm_num [ReserveCertificate, momentNumerator, Finset.sum_range_succ,
    Nat.stirlingSecond, Nat.descFactorial]

set_option maxHeartbeats 5000000 in
theorem reserveCertificate_pruned10 : ReserveCertificate 10 33 := by
  norm_num [ReserveCertificate, momentNumerator, Finset.sum_range_succ,
    Nat.stirlingSecond, Nat.descFactorial]

theorem requested_fors_reserve {b n : Nat} (hpair : (b, n) ∈ requestedLifetimePairs) :
    forsBound b n ≤ (63 : ℝ) / 64 / 2 ^ 127 := by
  apply forsBound_le_of_reserveCertificate
  simp only [requestedLifetimePairs, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hpair
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact reserveCertificate_full
  · exact reserveCertificate_pruned20
  · exact reserveCertificate_pruned13
  · exact reserveCertificate_pruned14
  · exact reserveCertificate_pruned12
  · exact reserveCertificate_pruned10

theorem requested_bootstrap_coefficient {b n : Nat} (hpair : (b, n) ∈ requestedLifetimePairs) :
    Real.sqrt (((n : ℝ) * 2 ^ (26 - b)) * 2 ^ 56 * 2 ^ 10) / 2 ^ 128 ≤
      (1 : ℝ) / 2 ^ 79 := by
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ 128)).2
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · calc
      ((n : ℝ) * 2 ^ (26 - b)) * 2 ^ 56 * 2 ^ 10 ≤ 2 ^ 31 * 2 ^ 56 * 2 ^ 10 := by
        gcongr
        exact requested_scaled_lifetime hpair
      _ ≤ _ := by norm_num

/-- A reserve of 1/64 suffices even with the proposed square-root correction and an explicit
additional 2^-160 error. This theorem does not assume a game-to-bootstrap reduction. -/
theorem normalized_bootstrap_closes {x : ℝ} (hx : 0 ≤ x)
    (h : x ≤ (63 : ℝ) / 64 / 2 ^ 127 + (1 / 2 ^ 79) * Real.sqrt x + 1 / 2 ^ 160) :
    x ≤ (1 : ℝ) / 2 ^ 127 := by
  have hs := Real.sq_sqrt hx
  have hyoung : (1 : ℝ) / 2 ^ 79 * Real.sqrt x ≤ x / 256 + 1 / 2 ^ 152 := by
    have hsq := sq_nonneg (Real.sqrt x / 16 - 8 / 2 ^ 79)
    norm_num at hsq ⊢
    nlinarith only [hs, hsq]
  norm_num at h hyoung ⊢
  linarith only [h, hyoung]

end LeanSphincs.Lifetime
