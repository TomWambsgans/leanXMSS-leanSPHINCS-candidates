import LeanSphincs.LifetimeBank
import LeanSphincs.LifetimeTerminal

/-!
The future-coverage target-bank potential. Its initial fresh-target price is exactly the
checked binomial occupancy expression. Actual digest-block queries and independent disclosure
steps satisfy local potential inequalities even when their order and target pairs are adaptive.
Lifting an independent disclosure step to signing with adversarial prequeries remains separate.
-/

namespace LeanSphincs.Lifetime

open OracleComp OracleSpec ENNReal Concrete Completeness

attribute [local instance] Classical.propDecidable

theorem digestForecast_average {α : Type} (sk : Seeded.SecretKey) (candidate : DigestCandidate)
    (cache : QueryCache HashSpec) (sample : ProbComp α) (weight : α → MessageDigest → ℝ≥0∞) :
    (∑' value, Pr[= value | sample] * digestForecast sk candidate cache (weight value)) =
      digestForecast sk candidate cache (fun digest => ∑' value, Pr[= value | sample] * weight value digest) := by
  simp_rw [digestForecast_eq_expected_messageDigest, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro result
  apply tsum_congr
  intro value
  ring

theorem uniformDigestForecast_average {α : Type} (sample : ProbComp α)
    (weight : α → MessageDigest → ℝ≥0∞) :
    (∑' value, Pr[= value | sample] * uniformDigestForecast (weight value)) =
      uniformDigestForecast (fun digest => ∑' value, Pr[= value | sample] * weight value digest) := by
  simp only [uniformDigestForecast]
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro digest
  apply tsum_congr
  intro value
  ring

theorem digestBankValue_average {α : Type} (sk : Seeded.SecretKey) (bank : Finset DigestCandidate)
    (cache : QueryCache HashSpec) (sample : ProbComp α) (weight : α → MessageDigest → ℝ≥0∞) :
    (∑' value, Pr[= value | sample] * digestBankValue sk bank cache (weight value)) =
      digestBankValue sk bank cache (fun digest => ∑' value, Pr[= value | sample] * weight value digest) := by
  simp only [digestBankValue, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro candidate _
  exact digestForecast_average sk candidate cache sample weight

variable [Params]

noncomputable def futureCoverWeight (parameter : PublicParameter) (remaining : Nat)
    (prior : Finset KeptDigestView) (digest : MessageDigest) : ℝ≥0∞ :=
  if Landed parameter (digestIndex digest) then
    Pr[ViewCovered (localDigestView digest) | uniformDisclosureSet remaining prior] else 0

theorem futureCoverWeight_zero (parameter : PublicParameter) (prior : Finset KeptDigestView)
    (digest : MessageDigest) : futureCoverWeight parameter 0 prior digest =
      if Landed parameter (digestIndex digest) ∧ ViewCovered (localDigestView digest) prior then 1 else 0 := by
  simp only [futureCoverWeight, uniformDisclosureSet_zero, probEvent_pure]
  split_ifs <;> simp_all

theorem futureCoverWeight_succ (parameter : PublicParameter) (remaining : Nat)
    (prior : Finset KeptDigestView) (digest : MessageDigest) :
    futureCoverWeight parameter (remaining + 1) prior digest =
      ∑' view, Pr[= view | ($ᵗ KeptDigestView : ProbComp KeptDigestView)] *
        futureCoverWeight parameter remaining (insert view prior) digest := by
  by_cases hland : Landed parameter (digestIndex digest)
  · simp only [futureCoverWeight, hland, if_true, uniformDisclosureSet_succ, probEvent_bind_eq_tsum]
  · simp only [futureCoverWeight, hland, if_false, mul_zero, tsum_zero]

/-- The initial fresh-target forecast is the exact occupancy expression already checked for
each requested lifetime, including the distinct-leaf correction needed at those limits. -/
theorem initial_futureCoverWeight (parameter : PublicParameter) (remaining : Nat) :
    uniformDigestForecast (futureCoverWeight parameter remaining ∅) =
      forsBoundENNReal subtreeHeight remaining := by
  unfold uniformDigestForecast
  simp_rw [futureCoverWeight, probEvent_uniformDisclosureSet_covered]
  let mass := SphincsSecurity.Concrete.binomialAverage ((2 : ℝ≥0∞) ^ subtreeHeight)⁻¹ remaining
    (fun r => (1 - (1 - (1 : ℝ≥0∞) / 1024) ^ r) ^ 24)
  change (∑' digest, Pr[= digest | ($ᵗ MessageDigest : ProbComp MessageDigest)] *
    (if Landed parameter (digestIndex digest) then mass else 0)) = _
  calc
    _ = Pr[fun digest => Landed parameter (digestIndex digest) |
          ($ᵗ MessageDigest : ProbComp MessageDigest)] * mass := by
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro digest
      split_ifs <;> simp
    _ = _ := by
      rw [probEvent_fullDigest_landed]
      unfold forsBoundENNReal
      congr 1
      rw [Nat.cast_pow, Nat.cast_ofNat, ENNReal.inv_pow]
      have hb : subtreeHeight ≤ 26 := Params.subtreeHeight_le
      simpa only [totalHeight, Nat.add_sub_of_le hb] using
        (two_pow_div_two_pow subtreeHeight (26 - subtreeHeight)).symm

noncomputable def futureBankPotential (sk : Seeded.SecretKey) (queries remaining : Nat)
    (prior : Finset KeptDigestView) (state : DigestBankState) : ℝ≥0∞ :=
  digestBankValue sk state.1 state.2 (futureCoverWeight sk.parameter remaining prior) +
    queries * uniformDigestForecast (futureCoverWeight sk.parameter remaining prior)

/-- Spend one actual digest-block query: the forecast of existing candidates is preserved,
and the reserve pays for at most one new candidate. All cached-block orders are included. -/
theorem futureBankPotential_query (sk : Seeded.SecretKey) (queries remaining : Nat)
    (prior : Finset KeptDigestView) (state : DigestBankState)
    (hrecorded : DigestQueriesRecorded sk state.1 state.2) (candidate : DigestCandidate) (call : Fin 2) :
    (∑' next, Pr[= next | digestBankStep sk candidate call state] *
      futureBankPotential sk queries remaining prior next) ≤
        futureBankPotential sk (queries + 1) remaining prior state := by
  simp only [futureBankPotential, mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
  calc
    _ ≤ (digestBankValue sk state.1 state.2 (futureCoverWeight sk.parameter remaining prior) +
        uniformDigestForecast (futureCoverWeight sk.parameter remaining prior)) +
          queries * uniformDigestForecast (futureCoverWeight sk.parameter remaining prior) :=
      add_le_add (expected_digestBankStep_le sk candidate call state hrecorded _)
        (mul_le_of_le_one_left' tsum_probOutput_le_one)
    _ = _ := by rw [Nat.cast_add, Nat.cast_one]; ring

/-- Spend one independent disclosure. This is an equality, so the adversary can choose when
to reveal further digest blocks from the entire preceding disclosure and query history. -/
theorem futureBankPotential_disclosure (sk : Seeded.SecretKey) (queries remaining : Nat)
    (prior : Finset KeptDigestView) (state : DigestBankState) :
    (∑' view, Pr[= view | ($ᵗ KeptDigestView : ProbComp KeptDigestView)] *
      futureBankPotential sk queries remaining (insert view prior) state) =
        futureBankPotential sk queries (remaining + 1) prior state := by
  simp only [futureBankPotential, mul_add, ENNReal.tsum_add]
  have havg : (fun digest => ∑' view, Pr[= view | ($ᵗ KeptDigestView : ProbComp KeptDigestView)] *
      futureCoverWeight sk.parameter remaining (insert view prior) digest) =
      futureCoverWeight sk.parameter (remaining + 1) prior :=
    funext fun digest => (futureCoverWeight_succ sk.parameter remaining prior digest).symm
  rw [digestBankValue_average, havg]
  congr 1
  calc
    _ = queries * ∑' view, Pr[= view | ($ᵗ KeptDigestView : ProbComp KeptDigestView)] *
        uniformDigestForecast (futureCoverWeight sk.parameter remaining (insert view prior)) := by
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro view
      ring
    _ = _ := by rw [uniformDigestForecast_average, havg]

theorem initial_futureBankPotential (sk : Seeded.SecretKey) (queries remaining : Nat)
    (cache : QueryCache HashSpec) :
    futureBankPotential sk queries remaining ∅ (∅, cache) =
      queries * forsBoundENNReal subtreeHeight remaining := by
  simp only [futureBankPotential, digestBankValue, Finset.sum_empty, zero_add,
    initial_futureCoverWeight]

/-- A completed, covered candidate contributes one at the terminal boundary. -/
theorem covered_candidate_le_futureBankPotential (sk : Seeded.SecretKey) (queries : Nat)
    (prior : Finset KeptDigestView) (state : DigestBankState) (candidate : DigestCandidate)
    (hmem : candidate ∈ state.1) (first second : HashOutput)
    (hfirst : state.2 (candidateInput sk candidate 0) = some first)
    (hsecond : state.2 (candidateInput sk candidate 1) = some second)
    (hland : Landed sk.parameter (blockIndex first))
    (hcovered : ViewCovered (localDigestView (truncateMessageDigest first second)) prior) :
    1 ≤ futureBankPotential sk queries 0 prior state := by
  have hone : digestForecast sk candidate state.2 (futureCoverWeight sk.parameter 0 prior) = 1 := by
    simp only [digestForecast, hfirst, hsecond, blockForecast_both, futureCoverWeight_zero,
      digestIndex_truncate, hland, hcovered, and_self, if_true]
  have hbank : 1 ≤ digestBankValue sk state.1 state.2 (futureCoverWeight sk.parameter 0 prior) := by
    rw [← hone]
    unfold digestBankValue
    exact Finset.single_le_sum
      (f := fun target => digestForecast sk target state.2 (futureCoverWeight sk.parameter 0 prior))
      (fun _ _ => bot_le) hmem
  exact hbank.trans le_self_add

end LeanSphincs.Lifetime
