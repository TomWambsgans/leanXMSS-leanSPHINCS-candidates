import LeanSphincs.LifetimePoolRatio
import LeanSphincs.LifetimeGrinding

/-! Exact accepted-index distribution of finite grinding against a fixed full randomizer
pool. It includes exhaustion and repeated draws; the pool itself need not be random. -/

namespace LeanSphincs.Lifetime
open OracleComp OracleSpec ENNReal Concrete Completeness

variable [Params]

theorem poolAcceptedCount_eq_card (parameter : PublicParameter) (pool : IndexPool) :
    poolAcceptedCount parameter pool = (Finset.univ.filter (fun rho => Landed parameter (pool rho))).card := by
  unfold poolAcceptedCount poolCount
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
    Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset Randomness)
      (Finset.univ.filter (Landed parameter)) pool

attribute [local irreducible] poolCount poolAcceptedCount

noncomputable def poolGrind (parameter : PublicParameter) (pool : IndexPool) : Nat → ProbComp (Option Index)
  | 0 => pure none
  | attempts + 1 => do
      let rho ← $ᵗ Randomness
      if Landed parameter (pool rho) then pure (some (pool rho)) else poolGrind parameter pool attempts

omit [Params] in
theorem pool_uniform_index (pool : IndexPool) (index : Index) :
    Pr[fun rho => pool rho = index | ($ᵗ Randomness : ProbComp Randomness)] =
      (poolCount index pool : ℝ≥0∞) / 2 ^ 128 := by
  rw [probEvent_uniformSample]
  simp only [poolCount, Randomness, card_bitVec, digestBits, Nat.cast_pow, Nat.cast_ofNat]

theorem pool_uniform_landing (parameter : PublicParameter) (pool : IndexPool) :
    Pr[fun rho => Landed parameter (pool rho) | ($ᵗ Randomness : ProbComp Randomness)] =
      (poolAcceptedCount parameter pool : ℝ≥0∞) / 2 ^ 128 := by
  rw [probEvent_uniformSample, poolAcceptedCount_eq_card]
  simp only [Randomness, card_bitVec, digestBits, Nat.cast_pow, Nat.cast_ofNat]

theorem poolGrind_index_factor (parameter : PublicParameter) (pool : IndexPool)
    (hpositive : 0 < poolAcceptedCount parameter pool) (index : Index)
    (hland : Landed parameter index) (attempts : Nat) :
    Pr[fun result => result = some index | poolGrind parameter pool attempts] =
      Pr[fun result => result.isSome | poolGrind parameter pool attempts] *
        ((poolCount index pool : ℝ≥0∞) / poolAcceptedCount parameter pool) := by
  induction attempts with
  | zero => simp [poolGrind]
  | succ attempts ih =>
      rw [poolGrind]
      apply probEvent_branch_factor ($ᵗ Randomness : ProbComp Randomness)
        (fun rho => Landed parameter (pool rho)) (fun rho => pure (some (pool rho)))
        (fun _ => poolGrind parameter pool attempts)
      · have hleft (rho : Randomness) :
            (if Landed parameter (pool rho) then
              Pr[fun result : Option Index => result = some index | (pure (some (pool rho)) : ProbComp _)]
              else 0) = if pool rho = index then (1 : ℝ≥0∞) else 0 := by
          by_cases hindex : pool rho = index
          · simp [hindex, hland]
          · simp [hindex, Ne.symm hindex]
        simp_rw [hleft]
        simp only [probEvent_pure, Option.isSome_some, if_true]
        simp only [mul_ite, mul_one, mul_zero]
        rw [← probEvent_eq_tsum_ite, ← probEvent_eq_tsum_ite,
          pool_uniform_index, pool_uniform_landing]
        have hc : (poolAcceptedCount parameter pool : ℝ≥0∞) ≠ 0 := by exact_mod_cast hpositive.ne'
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_natCast,
          ENNReal.toReal_pow, ENNReal.toReal_ofNat]
        have hp : (poolAcceptedCount parameter pool : ℝ) ≠ 0 := by exact_mod_cast hpositive.ne'
        field_simp
      · intro rho _
        exact ih

theorem poolGrind_index_le_ratio (parameter : PublicParameter) (pool : IndexPool)
    (hpositive : 0 < poolAcceptedCount parameter pool) (index : Index)
    (hland : Landed parameter index) (attempts : Nat) :
    Pr[fun result => result = some index | poolGrind parameter pool attempts] ≤
      (poolCount index pool : ℝ≥0∞) / poolAcceptedCount parameter pool := by
  rw [poolGrind_index_factor parameter pool hpositive index hland attempts]
  exact mul_le_of_le_one_left (by positivity) probEvent_le_one

theorem balanced_poolGrind_index_bound (parameter : PublicParameter) (pool : IndexPool)
    (hbalanced : PoolBalanced pool) (index : Index) (hland : Landed parameter index) (attempts : Nat) :
    Pr[fun result => result = some index | poolGrind parameter pool attempts] ≤
      (1 + (1 : ℝ≥0∞) / 2 ^ 18) / ((2 ^ subtreeHeight : Nat) : ℝ≥0∞) := by
  have hp : 0 < poolAcceptedCount parameter pool := by
    exact_mod_cast hbalanced.accepted_positive parameter
  refine (poolGrind_index_le_ratio parameter pool hp index hland attempts).trans ?_
  have h := ENNReal.ofReal_le_ofReal (hbalanced.accepted_index_ratio parameter index)
  have hnum : ENNReal.ofReal (1 + (1 : ℝ) / 2 ^ 18) =
      1 + (1 : ℝ≥0∞) / 2 ^ 18 := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_div_of_pos (by positivity)]
    norm_num
  simpa only [ENNReal.ofReal_div_of_pos (by exact_mod_cast hp : (0 : ℝ) < poolAcceptedCount parameter pool),
    ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < ((2 ^ subtreeHeight : Nat) : ℝ)),
    ENNReal.ofReal_natCast, hnum] using h

/-- The same finite sampler retaining the accepted randomizer, hence every FORS selector. -/
noncomputable def poolGrindRandomness (parameter : PublicParameter) (pool : IndexPool) :
    Nat → ProbComp (Option Randomness)
  | 0 => pure none
  | attempts + 1 => do
      let rho ← $ᵗ Randomness
      if Landed parameter (pool rho) then pure (some rho)
      else poolGrindRandomness parameter pool attempts

theorem poolGrindRandomness_factor (parameter : PublicParameter) (pool : IndexPool)
    (hpositive : 0 < poolAcceptedCount parameter pool) (rho : Randomness) (attempts : Nat) :
    Pr[fun result => result = some rho | poolGrindRandomness parameter pool attempts] =
      Pr[fun result => result.isSome | poolGrindRandomness parameter pool attempts] *
        ((if Landed parameter (pool rho) then 1 else 0) /
          (poolAcceptedCount parameter pool : ℝ≥0∞)) := by
  induction attempts with
  | zero => simp [poolGrindRandomness]
  | succ attempts ih =>
      rw [poolGrindRandomness]
      apply probEvent_branch_factor ($ᵗ Randomness : ProbComp Randomness)
        (fun r => Landed parameter (pool r)) (fun r => pure (some r))
        (fun _ => poolGrindRandomness parameter pool attempts)
      · by_cases hland : Landed parameter (pool rho)
        · have hleft (r : Randomness) :
              (if Landed parameter (pool r) then
                Pr[fun result => result = some rho | (pure (some r) : ProbComp _)] else 0) =
                if r = rho then (1 : ℝ≥0∞) else 0 := by
            by_cases heq : r = rho
            · simp [heq, hland]
            · simp [heq, Ne.symm heq]
          simp_rw [hleft]
          simp only [probEvent_pure, Option.isSome_some, if_true, hland]
          simp only [mul_ite, mul_one, mul_zero]
          rw [← probEvent_eq_tsum_ite, ← probEvent_eq_tsum_ite,
            pool_uniform_landing, probEvent_uniformSample]
          simp only [Finset.filter_eq', Finset.mem_univ, if_true, Finset.card_singleton,
            Nat.cast_one, Randomness, card_bitVec, digestBits, Nat.cast_pow, Nat.cast_ofNat]
          apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
          simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_natCast,
            ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_one]
          have hp : (poolAcceptedCount parameter pool : ℝ) ≠ 0 := by exact_mod_cast hpositive.ne'
          field_simp
        · have hleft (r : Randomness) :
              (if Landed parameter (pool r) then
                Pr[fun result => result = some rho | (pure (some r) : ProbComp _)] else 0) = (0 : ℝ≥0∞) := by
            by_cases heq : r = rho
            · simp [heq, hland]
            · simp [heq, Ne.symm heq]
          simp_rw [hleft]
          simp only [hland, if_false, ENNReal.zero_div, mul_zero, tsum_zero]
      · intro r _
        exact ih

/-- Exact accepted-source weighted law, retaining exhaustion as its success multiplier. -/
theorem poolGrindRandomness_weighted (parameter : PublicParameter) (pool : IndexPool)
    (hpositive : 0 < poolAcceptedCount parameter pool) (attempts : Nat)
    (weight : Randomness → ℝ≥0∞) :
    (∑ rho, Pr[= some rho | poolGrindRandomness parameter pool attempts] * weight rho) =
      (Pr[fun result => result.isSome | poolGrindRandomness parameter pool attempts] /
        (poolAcceptedCount parameter pool : ℝ≥0∞)) *
          ∑ rho ∈ Finset.univ.filter (fun r => Landed parameter (pool r)), weight rho := by
  simp only [← probEvent_eq_eq_probOutput]
  simp_rw [poolGrindRandomness_factor parameter pool hpositive]
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho _
  by_cases h : Landed parameter (pool rho) <;> simp [h, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

end LeanSphincs.Lifetime
