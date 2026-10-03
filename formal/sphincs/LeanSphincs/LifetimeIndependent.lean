import LeanSphincs.LifetimeSampling

/-! An explicit independent FORS reuse experiment, including the probability that a fresh
26-bit target index lands in a kept subtree of size `2^b`. -/

namespace LeanSphincs.Lifetime

open OracleComp OracleSpec ENNReal

def initialSubtreeEquiv (b : Nat) (hb : b ≤ 26) :
    Fin (2 ^ b) ≃ {index : Fin (2 ^ 26) // index.val < 2 ^ b} where
  toFun index := ⟨⟨index.val, index.isLt.trans_le (Nat.pow_le_pow_right (by omega) hb)⟩,
    index.isLt⟩
  invFun index := ⟨index.val.val, index.property⟩
  left_inv := by intro index; rfl
  right_inv := by intro index; rfl

theorem probEvent_initialSubtree (b : Nat) (hb : b ≤ 26) :
    Pr[fun index : Fin (2 ^ 26) => index.val < 2 ^ b |
      ($ᵗ Fin (2 ^ 26) : ProbComp (Fin (2 ^ 26)))] =
        (2 : ℝ≥0∞) ^ b / 2 ^ 26 := by
  rw [probEvent_uniformSample, ← Fintype.card_subtype,
    ← Fintype.card_congr (initialSubtreeEquiv b hb)]
  simp
  norm_num

/-- The fresh FORS target coordinates are sampled independently of all disclosed leaves. -/
noncomputable def independentTargetCoverageRandom (b n : Nat) (index : Fin (2 ^ b)) :
    ProbComp Bool := do
  let target ← $ᵗ (Fin 24 → Fin 1024)
  independentTargetCoverage b n index target

theorem probEvent_independentTargetCoverageRandom (b n : Nat) (index : Fin (2 ^ b)) :
    Pr[fun result => result = true | independentTargetCoverageRandom b n index] =
      SphincsSecurity.Concrete.binomialAverage ((2 : ℝ≥0∞) ^ b)⁻¹ n
        (fun r => (1 - (1 - (1 : ℝ≥0∞) / 1024) ^ r) ^ 24) := by
  rw [independentTargetCoverageRandom, probEvent_bind_eq_tsum]
  simp_rw [probEvent_independentTargetCoverage]
  rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (probFailure_uniformSample _), one_mul]

/-- A fresh global target, independent uniform signing indices, and independent FORS leaves.
The kept subtree is the initial interval; translations to any other subtree have the same law. -/
noncomputable def independentForgery (b n : Nat) : ProbComp Bool := do
  let index ← $ᵗ Fin (2 ^ 26)
  if h : index.val < 2 ^ b then
    independentTargetCoverageRandom b n ⟨index.val, h⟩
  else pure false

theorem probEvent_independentForgery (b n : Nat) (hb : b ≤ 26) :
    Pr[fun result => result = true | independentForgery b n] = forsBoundENNReal b n := by
  let mass := SphincsSecurity.Concrete.binomialAverage ((2 : ℝ≥0∞) ^ b)⁻¹ n
    (fun r => (1 - (1 - (1 : ℝ≥0∞) / 1024) ^ r) ^ 24)
  have hbranch (index : Fin (2 ^ 26)) :
      Pr[fun result => result = true |
        (if h : index.val < 2 ^ b then independentTargetCoverageRandom b n ⟨index.val, h⟩
          else pure false)] = if index.val < 2 ^ b then mass else 0 := by
    split_ifs with h
    · exact probEvent_independentTargetCoverageRandom b n _
    · simp
  rw [independentForgery, probEvent_bind_eq_tsum]
  simp_rw [hbranch]
  calc
    _ = (∑' index : Fin (2 ^ 26), if index.val < 2 ^ b then
          Pr[= index | ($ᵗ Fin (2 ^ 26) : ProbComp (Fin (2 ^ 26)))] else 0) * mass := by
      rw [← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro index
      by_cases h : index.val < 2 ^ b <;> simp [h]
    _ = Pr[fun index : Fin (2 ^ 26) => index.val < 2 ^ b |
          ($ᵗ Fin (2 ^ 26) : ProbComp (Fin (2 ^ 26)))] * mass := by
      rw [probEvent_eq_tsum_ite]
    _ = _ := by rw [probEvent_initialSubtree b hb]; rfl

theorem independent_forgery_lifetime_full {n : Nat} (hn : n ≤ 1200000000) :
    Pr[fun result => result = true | independentForgery 26 n] ≤ (1 : ℝ≥0∞) / 2 ^ 127 := by
  rw [probEvent_independentForgery _ _ (by omega)]
  exact fors_lifetime_ennreal_full hn

theorem independent_forgery_lifetime_pruned20 {n : Nat} (hn : n ≤ 23700000) :
    Pr[fun result => result = true | independentForgery 20 n] ≤ (1 : ℝ≥0∞) / 2 ^ 127 := by
  rw [probEvent_independentForgery _ _ (by omega)]
  exact fors_lifetime_ennreal_pruned20 hn

theorem independent_forgery_lifetime_pruned13 {n : Nat} (hn : n ≤ 240000) :
    Pr[fun result => result = true | independentForgery 13 n] ≤ (1 : ℝ≥0∞) / 2 ^ 127 := by
  rw [probEvent_independentForgery _ _ (by omega)]
  exact fors_lifetime_ennreal_pruned13 hn

theorem independent_forgery_lifetime_pruned14 {n : Nat} (hn : n ≤ 460000) :
    Pr[fun result => result = true | independentForgery 14 n] ≤ (1 : ℝ≥0∞) / 2 ^ 127 := by
  rw [probEvent_independentForgery _ _ (by omega)]
  exact fors_lifetime_ennreal_pruned14 hn

theorem independent_forgery_lifetime_pruned12 {n : Nat} (hn : n ≤ 125000) :
    Pr[fun result => result = true | independentForgery 12 n] ≤ (1 : ℝ≥0∞) / 2 ^ 127 := by
  rw [probEvent_independentForgery _ _ (by omega)]
  exact fors_lifetime_ennreal_pruned12 hn

theorem independent_forgery_lifetime_pruned10 {n : Nat} (hn : n ≤ 33) :
    Pr[fun result => result = true | independentForgery 10 n] ≤ (1 : ℝ≥0∞) / 2 ^ 127 := by
  rw [probEvent_independentForgery _ _ (by omega)]
  exact fors_lifetime_ennreal_pruned10 hn

end LeanSphincs.Lifetime
