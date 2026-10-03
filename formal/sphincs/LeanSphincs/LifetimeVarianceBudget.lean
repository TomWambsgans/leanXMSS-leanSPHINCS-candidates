import LeanSphincs.LifetimeBounds
import Mathlib.Analysis.Real.Sqrt

/-! Arithmetic for the proposed localized source-variance route. This checks its numerical
budget at the six unchanged lifetimes; it does not assert that the adaptive signing game has
already been coupled to that variance expression. -/

namespace LeanSphincs.Lifetime

set_option exponentiation.threshold 512

def requestedLifetimePairs : Finset (Nat × Nat) :=
  {(26, 1200000000), (20, 23700000), (13, 240000), (14, 460000), (12, 125000), (10, 33)}

theorem requested_scaled_lifetime {b n : Nat} (hpair : (b, n) ∈ requestedLifetimePairs) :
    (n : ℝ) * 2 ^ (26 - b) ≤ 2 ^ 31 := by
  simp only [requestedLifetimePairs, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hpair
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num

theorem requested_pair_fors_bound {b n : Nat} (hpair : (b, n) ∈ requestedLifetimePairs) :
    forsBound b n ≤ (1 : ℝ) / 2 ^ 127 := by
  simp only [requestedLifetimePairs, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hpair
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact fors_lifetime_full
  · exact fors_lifetime_pruned20
  · exact fors_lifetime_pruned13
  · exact fors_lifetime_pruned14
  · exact fors_lifetime_pruned12
  · exact fors_lifetime_pruned10

noncomputable def localizedVarianceRate (b n queries : Nat) : ℝ :=
  Real.sqrt (24 * ((n : ℝ) * 2 ^ (26 - b)) * forsBound b n *
    (1 + (queries : ℝ) / 2 ^ 74)) / 2 ^ 128

/-- With the proposed `2^-74` localized off-diagonal cap, the square-root variance charge
would cost at most `2^-146` per hash query. The hypothesis `q≤2^127` is the nontrivial range
of the requested final probability bound. -/
theorem requested_localizedVarianceRate {b n queries : Nat}
    (hpair : (b, n) ∈ requestedLifetimePairs) (hqueries : queries ≤ 2 ^ 127) :
    localizedVarianceRate b n queries ≤ (1 : ℝ) / 2 ^ 146 := by
  have hq : (queries : ℝ) ≤ 2 ^ 127 := by exact_mod_cast hqueries
  have hscaled := requested_scaled_lifetime hpair
  have hprice := requested_pair_fors_bound hpair
  have hproduct : 24 * ((n : ℝ) * 2 ^ (26 - b)) * forsBound b n *
      (1 + (queries : ℝ) / 2 ^ 74) ≤
        24 * (2 : ℝ) ^ 31 * (1 / 2 ^ 127) * (1 + 2 ^ 127 / 2 ^ 74) := by
    gcongr
    · exact forsBound_nonneg b n
  unfold localizedVarianceRate
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ 128)).2
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · exact hproduct.trans (by norm_num)

theorem localized_variance_exception_budget :
    (1 : ℝ) / 2 ^ 146 + 1 / 2 ^ 280 ≤ 1 / 2 ^ 145 := by norm_num

end LeanSphincs.Lifetime
