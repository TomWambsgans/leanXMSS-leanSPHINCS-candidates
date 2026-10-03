import LeanSphincs.LifetimeReserveBudget

/-! Arithmetic for a marked-source expansion at small hash-query budgets. These certificates
do not assert that the actual signing experiment admits the proposed expansion. -/

namespace LeanSphincs.Lifetime
set_option exponentiation.threshold 2048

set_option maxHeartbeats 5000000 in
theorem reserveCertificate_full_extra16 : ReserveCertificate 26 1200000016 := by
  norm_num [ReserveCertificate, momentNumerator, Finset.sum_range_succ,
    Nat.stirlingSecond, Nat.descFactorial]

set_option maxHeartbeats 5000000 in
theorem reserveCertificate_pruned20_extra16 : ReserveCertificate 20 23700016 := by
  norm_num [ReserveCertificate, momentNumerator, Finset.sum_range_succ,
    Nat.stirlingSecond, Nat.descFactorial]

set_option maxHeartbeats 5000000 in
theorem reserveCertificate_pruned13_extra16 : ReserveCertificate 13 240016 := by
  norm_num [ReserveCertificate, momentNumerator, Finset.sum_range_succ,
    Nat.stirlingSecond, Nat.descFactorial]

set_option maxHeartbeats 5000000 in
theorem reserveCertificate_pruned14_extra16 : ReserveCertificate 14 460016 := by
  norm_num [ReserveCertificate, momentNumerator, Finset.sum_range_succ,
    Nat.stirlingSecond, Nat.descFactorial]

set_option maxHeartbeats 5000000 in
theorem reserveCertificate_pruned12_extra16 : ReserveCertificate 12 125016 := by
  norm_num [ReserveCertificate, momentNumerator, Finset.sum_range_succ,
    Nat.stirlingSecond, Nat.descFactorial]

set_option maxHeartbeats 5000000 in
theorem reserveCertificate_pruned10_extra16 : ReserveCertificate 10 49 := by
  norm_num [ReserveCertificate, momentNumerator, Finset.sum_range_succ,
    Nat.stirlingSecond, Nat.descFactorial]

theorem requested_fors_extra16_reserve {b n : Nat}
    (hpair : (b, n) ∈ requestedLifetimePairs) :
    forsBound b (n + 16) ≤ (63 : ℝ) / 64 / 2 ^ 127 := by
  apply forsBound_le_of_reserveCertificate
  simp only [requestedLifetimePairs, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq] at hpair
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact reserveCertificate_full_extra16
  · exact reserveCertificate_pruned20_extra16
  · exact reserveCertificate_pruned13_extra16
  · exact reserveCertificate_pruned14_extra16
  · exact reserveCertificate_pruned12_extra16
  · exact reserveCertificate_pruned10_extra16

/-- The factor two is the coarse loss from the globally balanced accepted-randomizer pool. -/
noncomputable def markedSourceRatio (b n : Nat) (q : ℝ) : ℝ :=
  2 * ((n : ℝ) * 2 ^ (26 - b)) * q / 2 ^ 128

theorem markedSourceRatio_nonneg (b n : Nat) {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ markedSourceRatio b n q := by
  unfold markedSourceRatio
  positivity

theorem requested_markedSourceRatio_le {b n : Nat}
    (hpair : (b, n) ∈ requestedLifetimePairs) {q : ℝ} (hq : 0 ≤ q) :
    markedSourceRatio b n q ≤ q / 2 ^ 96 := by
  have hn := requested_scaled_lifetime hpair
  unfold markedSourceRatio
  calc
    2 * ((n : ℝ) * 2 ^ (26 - b)) * q / 2 ^ 128 ≤
        2 * 2 ^ 31 * q / 2 ^ 128 := by gcongr
    _ = q / 2 ^ 96 := by ring

theorem requested_markedSourceRatio_small {b n : Nat}
    (hpair : (b, n) ∈ requestedLifetimePairs) {q : ℝ}
    (hq : 0 ≤ q) (hsmall : q ≤ 2 ^ 88) :
    markedSourceRatio b n q ≤ (1 : ℝ) / 2 ^ 8 := by
  calc
    markedSourceRatio b n q ≤ q / 2 ^ 96 := requested_markedSourceRatio_le hpair hq
    _ ≤ 2 ^ 88 / 2 ^ 96 := by gcongr
    _ = (1 : ℝ) / 2 ^ 8 := by norm_num

theorem requested_markedSourceRatio_tail {b n : Nat}
    (hpair : (b, n) ∈ requestedLifetimePairs) {q : ℝ}
    (hq : 0 ≤ q) (hsmall : q ≤ 2 ^ 88) :
    markedSourceRatio b n q ^ 16 ≤ q / 2 ^ 216 := by
  have hr := requested_markedSourceRatio_le hpair hq
  have hp : q ^ 15 ≤ (2 ^ 88 : ℝ) ^ 15 := by gcongr
  calc
    markedSourceRatio b n q ^ 16 ≤ (q / 2 ^ 96) ^ 16 := by
      exact pow_le_pow_left₀ (markedSourceRatio_nonneg b n hq) hr 16
    _ = q * q ^ 15 / 2 ^ 1536 := by ring
    _ ≤ q * (2 ^ 88) ^ 15 / 2 ^ 1536 := by gcongr
    _ = q / 2 ^ 216 := by ring

/-- The proposed finite expansion has spare room at every requested lifetime for
all query budgets through `2^88`, including its order-sixteen tail. -/
theorem requested_marked_expansion_budget {b n : Nat}
    (hpair : (b, n) ∈ requestedLifetimePairs) {q : ℝ}
    (hq : 0 ≤ q) (hsmall : q ≤ 2 ^ 88) :
    q * forsBound b (n + 16) / (1 - markedSourceRatio b n q) +
        markedSourceRatio b n q ^ 16 + q / 2 ^ 160 ≤ q / 2 ^ 127 := by
  have hδ := requested_markedSourceRatio_small hpair hq hsmall
  have hd : (255 : ℝ) / 256 ≤ 1 - markedSourceRatio b n q := by
    norm_num at hδ ⊢
    linarith
  have hdpos : 0 < 1 - markedSourceRatio b n q := lt_of_lt_of_le (by norm_num) hd
  have hF := requested_fors_extra16_reserve hpair
  have hmain : q * forsBound b (n + 16) / (1 - markedSourceRatio b n q) ≤
      q * ((63 : ℝ) / 64 / 2 ^ 127) / (255 / 256) := by
    apply (div_le_iff₀ hdpos).2
    calc
      q * forsBound b (n + 16) ≤ q * ((63 : ℝ) / 64 / 2 ^ 127) := by gcongr
      _ ≤ (q * ((63 : ℝ) / 64 / 2 ^ 127) / (255 / 256)) *
          (1 - markedSourceRatio b n q) := by
        calc
          _ = (q * ((63 : ℝ) / 64 / 2 ^ 127) / (255 / 256)) * (255 / 256) := by ring
          _ ≤ _ := by gcongr
  have ht := requested_markedSourceRatio_tail hpair hq hsmall
  calc
    _ ≤ q * ((63 : ℝ) / 64 / 2 ^ 127) / (255 / 256) + q / 2 ^ 216 + q / 2 ^ 160 := by
      linarith only [hmain, ht]
    _ ≤ q / 2 ^ 127 := by
      nlinarith only [hq]

end LeanSphincs.Lifetime
