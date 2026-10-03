import LeanSphincs.LifetimePairedMonitor
import LeanSphincs.SecurityExponentialCharge

/-! Source-query-budget exponential tails for the actual paired digest monitor. These bounds
apply to arbitrary adaptive OracleWorld programs, including arbitrarily many private samples. -/

namespace LeanSphincs.Lifetime
open OracleComp OracleSpec ENNReal Concrete Completeness Security Security.SeedCoupling
open Security.ExponentialCharge
set_option backward.isDefEq.respectTransparency false

noncomputable def pairedWorldHit (sk : Seeded.SecretKey) (event : MessageDigest → Prop) : HitTest
  | .inl _, _, _, _ => false
  | .inr input, before, _, after =>
      @decide (pairedHit sk event input before after) (Classical.propDecidable _)

theorem expected_bool_pow {α : Type} (sample : ProbComp α) (hit : α → Bool) (offset : Nat) :
    (∑' value, Pr[= value | sample] * ((offset + 1 : Nat) : ℝ≥0∞) ^
      (if hit value then 1 else 0)) = 1 + (offset : ℝ≥0∞) * Pr[fun value => hit value | sample] := by
  have hpoint (value : α) : ((offset + 1 : Nat) : ℝ≥0∞) ^ (if hit value then 1 else 0) =
      1 + (offset : ℝ≥0∞) * (if hit value then 1 else 0) := by
    cases hit value <;> simp [Nat.cast_add, add_comm]
  simp_rw [hpoint, mul_add, mul_one]
  rw [ENNReal.tsum_add, tsum_probOutput_of_liftM_PMF]
  simp_rw [mul_left_comm (Pr[= _ | sample]) (offset : ℝ≥0∞)]
  rw [ENNReal.tsum_mul_left]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← probEvent_eq_tsum_ite]

theorem paired_query_moment (sk : Seeded.SecretKey) (event : MessageDigest → Prop)
    (offset : Nat) (input : OracleWorld.Domain) (cache : QueryCache HashSpec)
    (hpaired : PairedCache sk cache) :
    (∑' result, Pr[= result | (pairedRom sk input).run cache] *
      ((offset + 1 : Nat) : ℝ≥0∞) ^
        (if pairedWorldHit sk event input cache result.1 result.2 then 1 else 0)) ≤
      (1 + (offset : ℝ≥0∞) * Pr[event | ($ᵗ MessageDigest : ProbComp MessageDigest)]) ^ queryCost input := by
  cases input with
  | inl input =>
      simp only [pairedWorldHit, Bool.false_eq_true, if_false, pow_zero, mul_one,
        tsum_probOutput_of_liftM_PMF, queryCost, le_rfl]
  | inr input =>
      rw [expected_bool_pow]
      simp only [queryCost, pow_one, pairedWorldHit, decide_eq_true_eq]
      exact add_le_add le_rfl (mul_le_mul' le_rfl (pairedHash_hit_le sk event input cache hpaired))

/-- The counted monitor erases to the original lazy-ROM program's result and source hash count. -/
theorem evalDist_paired_monitor_output {α : Type} (sk : Seeded.SecretKey)
    (event : MessageDigest → Prop) (program : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    𝒟[(fun result => (result.1, result.2.1)) <$>
        ExponentialCharge.run (pairedRom sk) (pairedWorldHit sk event) program cache] =
      𝒟[(simulateQ romImpl (countHashQueries program)).run' cache] := by
  have heq := congrArg (fun computation => Prod.fst <$> computation)
    (ExponentialCharge.run_erase (pairedRom sk) (pairedWorldHit sk event) program cache)
  simp only [Functor.map_map] at heq
  rw [heq]
  change 𝒟[(simulateQ (pairedRom sk) (countHashQueries program)).run' cache] = _
  exact (evalDist_pairedRom sk (countHashQueries program) cache).symm

theorem paired_monitor_hash_bound {α : Type} (sk : Seeded.SecretKey)
    (event : MessageDigest → Prop) (program : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (q : Nat) (hbound : ∀ result ∈ support ((simulateQ romImpl (countHashQueries program)).run' cache),
      result.2 ≤ q) :
    ∀ result ∈ support (ExponentialCharge.run (pairedRom sk) (pairedWorldHit sk event) program cache),
      result.2.1 ≤ q := by
  intro result hresult
  have hm : (result.1, result.2.1) ∈ support ((fun result => (result.1, result.2.1)) <$>
      ExponentialCharge.run (pairedRom sk) (pairedWorldHit sk event) program cache) := by
    rw [support_map]
    exact ⟨result, hresult, rfl⟩
  exact hbound _ ((mem_support_iff_of_evalDist_eq
    (evalDist_paired_monitor_output sk event program cache) _).mp hm)

theorem paired_monitor_normalized {α : Type} (sk : Seeded.SecretKey)
    (event : MessageDigest → Prop) (offset : Nat) (program : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hpaired : PairedCache sk cache) :
    (∑' result, Pr[= result |
        ExponentialCharge.run (pairedRom sk) (pairedWorldHit sk event) program cache] *
      (((offset + 1 : Nat) : ℝ≥0∞) ^ result.2.2.1 /
        (1 + (offset : ℝ≥0∞) * Pr[event | ($ᵗ MessageDigest : ProbComp MessageDigest)]) ^ result.2.1)) ≤ 1 := by
  apply ExponentialCharge.expected_normalized_le (pairedRom sk) (pairedWorldHit sk event)
    _ _ (by positivity) (ENNReal.add_ne_top.mpr ⟨by simp, ENNReal.mul_ne_top (by simp) probEvent_ne_top⟩) (PairedCache sk)
    (fun input cache h result hresult => (pairedRom_support_paired sk input cache h result.1 result.2 hresult).1)
    (paired_query_moment sk event offset) program cache hpaired

/-- The full adaptive fresh-candidate tail in terms of the ORIGINAL query counter. -/
theorem paired_monitor_tail {α : Type} (sk : Seeded.SecretKey)
    (event : MessageDigest → Prop) (offset : Nat) (program : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hpaired : PairedCache sk cache) (q threshold : Nat)
    (hbound : ∀ result ∈ support ((simulateQ romImpl (countHashQueries program)).run' cache), result.2 ≤ q) :
    Pr[fun result => threshold ≤ result.2.2.1 |
      ExponentialCharge.run (pairedRom sk) (pairedWorldHit sk event) program cache] ≤
        (1 + (offset : ℝ≥0∞) * Pr[event | ($ᵗ MessageDigest : ProbComp MessageDigest)]) ^ q /
          ((offset + 1 : Nat) : ℝ≥0∞) ^ threshold := by
  exact ExponentialCharge.tail_le_of_normalized
    (ExponentialCharge.run (pairedRom sk) (pairedWorldHit sk event) program cache)
    (fun result => result.2.1) (fun result => result.2.2.1)
    ((offset + 1 : Nat) : ℝ≥0∞)
    (1 + (offset : ℝ≥0∞) * Pr[event | ($ᵗ MessageDigest : ProbComp MessageDigest)])
    (by exact_mod_cast (show 1 ≤ offset + 1 by omega)) (by positivity) (by simp)
    (by simp) (by positivity)
    (ENNReal.add_ne_top.mpr ⟨by simp, ENNReal.mul_ne_top (by simp) probEvent_ne_top⟩) q threshold
    (paired_monitor_hash_bound sk event program cache q hbound)
    (paired_monitor_normalized sk event offset program cache hpaired)

end LeanSphincs.Lifetime
