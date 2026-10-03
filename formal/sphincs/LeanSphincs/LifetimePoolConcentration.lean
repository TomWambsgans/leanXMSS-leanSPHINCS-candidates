import LeanSphincs.LifetimeSampling
import LeanSphincs.Scheme
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Pi

/-! Concentration of the complete randomizer-index pool. This is an explicit independent
uniform table law; its use for adaptive messages requires the corresponding ROM table coupling.
The event is uniform over the whole pool and thus remains true after adaptive inspection. -/

namespace LeanSphincs.Lifetime

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal
set_option exponentiation.threshold 2048

abbrev IndexPool := Randomness → Index

noncomputable def indexPoolMeasure : Measure IndexPool :=
  Measure.pi (fun _ : Randomness => (PMF.uniformOfFintype Index).toMeasure)

instance : IsProbabilityMeasure indexPoolMeasure := by
  unfold indexPoolMeasure
  infer_instance

def poolHit (index : Index) (rho : Randomness) (pool : IndexPool) : ℝ :=
  if pool rho = index then 1 else 0

def poolCount (index : Index) (pool : IndexPool) : Nat :=
  (Finset.univ.filter (fun rho => pool rho = index)).card

theorem poolCount_eq_sum (index : Index) (pool : IndexPool) :
    (poolCount index pool : ℝ) = ∑ rho, poolHit index rho pool := by
  simp only [poolCount, poolHit, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero]

theorem poolHit_independent (index : Index) : iIndepFun (poolHit index) indexPoolMeasure := by
  exact iIndepFun_pi (X := fun _ value => if value = index then (1 : ℝ) else 0)
    (fun _ => (measurable_of_finite _).aemeasurable)

theorem poolHit_mean (index : Index) (rho : Randomness) :
    ∫ pool, poolHit index rho pool ∂indexPoolMeasure = (1 : ℝ) / 2 ^ 26 := by
  change (∫ pool : IndexPool, (if pool rho = index then (1 : ℝ) else 0)
    ∂Measure.pi (fun _ : Randomness => (PMF.uniformOfFintype Index).toMeasure)) = _
  rw [integral_comp_eval (μ := fun _ : Randomness => (PMF.uniformOfFintype Index).toMeasure)
    (i := rho) (f := fun value : Index => if value = index then (1 : ℝ) else 0)
    (measurable_of_finite _).aestronglyMeasurable]
  have hind : (fun value : Index => if value = index then (1 : ℝ) else 0) =
      Set.indicator {index} (fun _ => (1 : ℝ)) := by
    funext value
    simp only [Set.indicator, Set.mem_singleton_iff]
  rw [hind, integral_indicator (measurableSet_singleton index)]
  simp only [integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_one,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton index), PMF.uniformOfFintype_apply,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]
  norm_num [Index, totalHeight]

theorem poolHit_subGaussian (index : Index) (rho : Randomness) :
    HasSubgaussianMGF (fun pool => poolHit index rho pool - (1 : ℝ) / 2 ^ 26)
      (1 / 4 : ℝ≥0) indexPoolMeasure := by
  have h := hasSubgaussianMGF_of_mem_Icc (μ := indexPoolMeasure)
    (X := poolHit index rho) (a := 0) (b := 1) (measurable_of_finite _).aemeasurable
    (Filter.Eventually.of_forall (fun pool => by
      unfold poolHit
      split <;> constructor <;> norm_num))
  norm_num [poolHit_mean] at h ⊢
  exact h

/-- A single index's count in the full 128-bit randomizer pool is within relative2^-20
of its mean2^102 except with exponentially small probability. -/
theorem indexPool_upper_tail (index : Index) :
    indexPoolMeasure.real {pool | (2 : ℝ) ^ 82 ≤ (poolCount index pool : ℝ) - (2 : ℝ) ^ 102} ≤
      Real.exp (-(2 : ℝ) ^ 37) := by
  have hind := (poolHit_independent index).comp (fun _ value => value - (1 : ℝ) / 2 ^ 26)
    (fun _ => by fun_prop)
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind
    (s := Finset.univ) (c := fun _ : Randomness => (1 / 4 : ℝ≥0))
    (fun rho _ => poolHit_subGaussian index rho) (show 0 ≤ (2 : ℝ) ^ 82 by positivity)
  have hsum (pool : IndexPool) :
      (∑ rho : Randomness, (poolHit index rho pool - (1 : ℝ) / 2 ^ 26)) =
        (poolCount index pool : ℝ) - (2 : ℝ) ^ 102 := by
    rw [Finset.sum_sub_distrib, ← poolCount_eq_sum]
    simp only [Finset.sum_const, Finset.card_univ, Randomness, card_bitVec, digestBits, nsmul_eq_mul]
    have heq : ((2 ^ 128 : Nat) : ℝ) * (1 / 2 ^ 26) = 2 ^ 102 := by norm_num
    rw [heq]
  simp only [Function.comp_def, hsum] at h
  convert h using 1
  norm_num only [Finset.sum_const, Finset.card_univ, Randomness, card_bitVec, digestBits,
    nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast]
  norm_num

theorem indexPool_lower_tail (index : Index) :
    indexPoolMeasure.real {pool | (2 : ℝ) ^ 82 ≤ (2 : ℝ) ^ 102 - (poolCount index pool : ℝ)} ≤
      Real.exp (-(2 : ℝ) ^ 37) := by
  have hind := (poolHit_independent index).comp (fun _ value => -(value - (1 : ℝ) / 2 ^ 26))
    (fun _ => by fun_prop)
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind
    (s := Finset.univ) (c := fun _ : Randomness => (1 / 4 : ℝ≥0))
    (fun rho _ => (poolHit_subGaussian index rho).neg) (show 0 ≤ (2 : ℝ) ^ 82 by positivity)
  have hsum (pool : IndexPool) :
      (∑ rho : Randomness, -(poolHit index rho pool - (1 : ℝ) / 2 ^ 26)) =
        (2 : ℝ) ^ 102 - (poolCount index pool : ℝ) := by
    rw [Finset.sum_neg_distrib, Finset.sum_sub_distrib, ← poolCount_eq_sum]
    simp only [Finset.sum_const, Finset.card_univ, Randomness, card_bitVec, digestBits, nsmul_eq_mul]
    have heq : ((2 ^ 128 : Nat) : ℝ) * (1 / 2 ^ 26) = 2 ^ 102 := by norm_num
    rw [heq]
    ring
  simp only [Function.comp_def, hsum] at h
  convert h using 1
  norm_num only [Finset.sum_const, Finset.card_univ, Randomness, card_bitVec, digestBits,
    nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast]
  norm_num

def PoolBalanced (pool : IndexPool) : Prop :=
  ∀ index, |(poolCount index pool : ℝ) - (2 : ℝ) ^ 102| < (2 : ℝ) ^ 82

theorem indexPool_bad_index (index : Index) :
    indexPoolMeasure.real {pool | (2 : ℝ) ^ 82 ≤ |(poolCount index pool : ℝ) - (2 : ℝ) ^ 102|} ≤
      2 * Real.exp (-(2 : ℝ) ^ 37) := by
  have hset : {pool : IndexPool | (2 : ℝ) ^ 82 ≤ |(poolCount index pool : ℝ) - (2 : ℝ) ^ 102|} =
      {pool | (2 : ℝ) ^ 82 ≤ (poolCount index pool : ℝ) - (2 : ℝ) ^ 102} ∪
      {pool | (2 : ℝ) ^ 82 ≤ (2 : ℝ) ^ 102 - (poolCount index pool : ℝ)} := by
    ext pool
    simp only [Set.mem_setOf_eq, Set.mem_union, le_abs]
    constructor <;> intro h <;> rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rw [hset]
  exact (measureReal_union_le _ _).trans
    ((add_le_add (indexPool_upper_tail index) (indexPool_lower_tail index)).trans_eq (by ring))

theorem indexPool_unbalanced :
    indexPoolMeasure.real {pool | ¬PoolBalanced pool} ≤
      (2 : ℝ) ^ 27 * Real.exp (-(2 : ℝ) ^ 37) := by
  have hset : {pool : IndexPool | ¬PoolBalanced pool} =
      ⋃ index, {pool | (2 : ℝ) ^ 82 ≤ |(poolCount index pool : ℝ) - (2 : ℝ) ^ 102|} := by
    ext pool
    simp only [PoolBalanced, Set.mem_setOf_eq, not_forall, not_lt, Set.mem_iUnion]
  rw [hset]
  refine (measureReal_iUnion_fintype_le _).trans
    ((Finset.sum_le_sum (fun index _ => indexPool_bad_index index)).trans_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : Fintype.card Index = 2 ^ 26 := Fintype.card_fin _
  rw [hcard]
  ring

/-- The product-measure pool is exactly an independently uniform finite oracle table. -/
theorem indexPoolMeasure_eq_uniform :
    indexPoolMeasure = (PMF.uniformOfFintype IndexPool).toMeasure := by
  apply Measure.ext_of_singleton
  intro pool
  rw [indexPoolMeasure, Measure.pi_singleton]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, Finset.prod_const, Finset.card_univ, IndexPool,
    Fintype.card_fun, Nat.cast_pow, ENNReal.inv_pow]

/-- Parameter, root, and message are all quantified, so selecting any of them after inspecting
the table cannot invalidate the balanced-pool event. -/
abbrev PoolKey := PublicParameter × Digest × Message
abbrev IndexPoolFamily := PoolKey → IndexPool

noncomputable def indexPoolFamilyMeasure : Measure IndexPoolFamily :=
  Measure.pi (fun _ : PoolKey => indexPoolMeasure)

instance : IsProbabilityMeasure indexPoolFamilyMeasure := by
  unfold indexPoolFamilyMeasure
  infer_instance

def AllPoolsBalanced (family : IndexPoolFamily) : Prop := ∀ key, PoolBalanced (family key)

theorem poolFamily_unbalanced_key (key : PoolKey) :
    indexPoolFamilyMeasure.real {family | ¬PoolBalanced (family key)} ≤
      (2 : ℝ) ^ 27 * Real.exp (-(2 : ℝ) ^ 37) := by
  have h := (measurePreserving_eval (fun _ : PoolKey => indexPoolMeasure) key).measure_preimage
    ((Set.toFinite {pool | ¬PoolBalanced pool}).measurableSet.nullMeasurableSet)
  change (indexPoolFamilyMeasure ((fun family => family key) ⁻¹' {pool | ¬PoolBalanced pool})).toReal ≤ _
  rw [show indexPoolFamilyMeasure ((fun family => family key) ⁻¹' {pool | ¬PoolBalanced pool}) =
    indexPoolMeasure {pool | ¬PoolBalanced pool} from h]
  exact indexPool_unbalanced

theorem poolFamily_unbalanced :
    indexPoolFamilyMeasure.real {family | ¬AllPoolsBalanced family} ≤
      (2 : ℝ) ^ 539 * Real.exp (-(2 : ℝ) ^ 37) := by
  have hset : {family : IndexPoolFamily | ¬AllPoolsBalanced family} =
      ⋃ key, {family | ¬PoolBalanced (family key)} := by
    ext family
    simp only [AllPoolsBalanced, Set.mem_setOf_eq, not_forall, Set.mem_iUnion]
  rw [hset]
  refine (measureReal_iUnion_fintype_le _).trans
    ((Finset.sum_le_sum (fun key _ => poolFamily_unbalanced_key key)).trans_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : Fintype.card PoolKey = 2 ^ 512 := by
    rw [← Nat.card_eq_fintype_card]
    simp only [PoolKey, Nat.card_eq_fintype_card, PublicParameter, Digest, Message,
      publicParameterBits, digestBits, messageBits]
    norm_num
  rw [hcard]
  ring

theorem pool_concentration_exp_bound :
    (2 : ℝ) ^ 539 * Real.exp (-(2 : ℝ) ^ 37) ≤ (1 : ℝ) / 2 ^ 400 := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
  have hpow : (2 : ℝ) ^ 1024 ≤ Real.exp 1024 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) he 1024
    simpa only [← Real.exp_nat_mul, mul_one, Nat.cast_ofNat] using hp
  have hexp : Real.exp (-(2 : ℝ) ^ 37) ≤ (1 : ℝ) / 2 ^ 1024 := by
    calc
      Real.exp (-(2 : ℝ) ^ 37) ≤ Real.exp (-1024) := Real.exp_le_exp.mpr (by norm_num)
      _ = (1 : ℝ) / Real.exp 1024 := by rw [Real.exp_neg, one_div]
      _ ≤ (1 : ℝ) / 2 ^ 1024 := one_div_le_one_div_of_le (by positivity) hpow
  apply (mul_le_mul_of_nonneg_left hexp (by positivity)).trans
  norm_num

/-- Uniformly for every possible parameter/root/message, failure of relative2^-20 index-pool
balance has probability at most2^-400 in the independent finite table model. -/
theorem poolFamily_unbalanced_negligible :
    indexPoolFamilyMeasure.real {family | ¬AllPoolsBalanced family} ≤ (1 : ℝ) / 2 ^ 400 :=
  poolFamily_unbalanced.trans pool_concentration_exp_bound

theorem indexPoolFamilyMeasure_eq_uniform :
    indexPoolFamilyMeasure = (PMF.uniformOfFintype IndexPoolFamily).toMeasure := by
  apply Measure.ext_of_singleton
  intro family
  rw [indexPoolFamilyMeasure, Measure.pi_singleton]
  simp only [indexPoolMeasure_eq_uniform,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, Finset.prod_const, Finset.card_univ, IndexPoolFamily,
    Fintype.card_fun, Nat.cast_pow, ENNReal.inv_pow]

end LeanSphincs.Lifetime
