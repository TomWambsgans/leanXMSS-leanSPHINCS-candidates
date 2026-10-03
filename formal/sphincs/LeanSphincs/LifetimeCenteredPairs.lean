import LeanSphincs.LifetimeActiveBank

/-! Conditional centering for a fixed off-diagonal source/target kernel. A fresh pair is
both a possible source and a target; the same freshly sampled digest appears in both roles.
Double centering makes its complete increment mean zero. The square below retains the
covariance between those roles, rather than treating their answers as independent. -/

namespace LeanSphincs.Lifetime

open scoped BigOperators

variable {α ι : Type} [Fintype α]

noncomputable def finiteMean (weight : α → ℝ) (value : α → ℝ) : ℝ :=
  ∑ point, weight point * value point

noncomputable def pairSourceMean (weight : α → ℝ) (kernel : α → α → ℝ) (target : α) : ℝ :=
  finiteMean weight (fun source => kernel source target)

noncomputable def pairTargetMean (weight : α → ℝ) (kernel : α → α → ℝ) (source : α) : ℝ :=
  finiteMean weight (kernel source)

noncomputable def pairGrandMean (weight : α → ℝ) (kernel : α → α → ℝ) : ℝ :=
  finiteMean weight (pairTargetMean weight kernel)

noncomputable def centeredPairKernel (weight : α → ℝ) (kernel : α → α → ℝ)
    (source target : α) : ℝ :=
  kernel source target - pairSourceMean weight kernel target - pairTargetMean weight kernel source +
    pairGrandMean weight kernel

theorem finiteMean_const (weight : α → ℝ) (hmass : ∑ point, weight point = 1) (value : ℝ) :
    finiteMean weight (fun _ => value) = value := by
  rw [finiteMean, ← Finset.sum_mul, hmass, one_mul]

theorem finiteMean_add (weight : α → ℝ) (left right : α → ℝ) :
    finiteMean weight (fun point => left point + right point) =
      finiteMean weight left + finiteMean weight right := by
  simp only [finiteMean, mul_add, Finset.sum_add_distrib]

theorem finiteMean_sub (weight : α → ℝ) (left right : α → ℝ) :
    finiteMean weight (fun point => left point - right point) =
      finiteMean weight left - finiteMean weight right := by
  simp only [finiteMean, mul_sub, Finset.sum_sub_distrib]

theorem finiteMean_finsetSum (weight : α → ℝ) (bank : Finset ι) (value : ι → α → ℝ) :
    finiteMean weight (fun point => ∑ candidate ∈ bank, value candidate point) =
      ∑ candidate ∈ bank, finiteMean weight (value candidate) := by
  simp only [finiteMean, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem pairGrandMean_comm (weight : α → ℝ) (kernel : α → α → ℝ) :
    finiteMean weight (pairSourceMean weight kernel) = pairGrandMean weight kernel := by
  simp only [finiteMean, pairSourceMean, pairGrandMean, pairTargetMean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _
  apply Finset.sum_congr rfl
  intro target _
  ring

/-- Mean zero in the source coordinate. The target may already be fully cached. -/
theorem centeredPairKernel_source_mean (weight : α → ℝ) (hmass : ∑ point, weight point = 1)
    (kernel : α → α → ℝ) (target : α) :
    finiteMean weight (fun source => centeredPairKernel weight kernel source target) = 0 := by
  simp only [centeredPairKernel, finiteMean_add, finiteMean_sub, finiteMean_const weight hmass]
  change pairSourceMean weight kernel target - pairSourceMean weight kernel target -
    pairGrandMean weight kernel + pairGrandMean weight kernel = 0
  ring

/-- Mean zero in the target coordinate. This second compensation is essential when a new
query is added to the same bank that previously supplied cached signing sources. -/
theorem centeredPairKernel_target_mean (weight : α → ℝ) (hmass : ∑ point, weight point = 1)
    (kernel : α → α → ℝ) (source : α) :
    finiteMean weight (centeredPairKernel weight kernel source) = 0 := by
  change finiteMean weight (fun target => kernel source target - pairSourceMean weight kernel target -
    pairTargetMean weight kernel source + pairGrandMean weight kernel) = 0
  simp only [finiteMean_add, finiteMean_sub, finiteMean_const weight hmass, pairGrandMean_comm]
  change pairTargetMean weight kernel source - pairGrandMean weight kernel -
    pairTargetMean weight kernel source + pairGrandMean weight kernel = 0
  ring

noncomputable def sourcePairIncrement (weight : α → ℝ) (kernel : α → α → ℝ)
    (targets : Finset ι) (digest : ι → α) (newSource : Bool) (fresh : α) : ℝ :=
  if newSource then ∑ target ∈ targets, centeredPairKernel weight kernel fresh (digest target) else 0

noncomputable def targetPairIncrement (weight : α → ℝ) (kernel : α → α → ℝ)
    (sources : Finset ι) (digest : ι → α) (fresh : α) : ℝ :=
  ∑ source ∈ sources, centeredPairKernel weight kernel (digest source) fresh

noncomputable def offDiagonalPairIncrement (weight : α → ℝ) (kernel : α → α → ℝ)
    (sources targets : Finset ι) (digest : ι → α) (newSource : Bool) (fresh : α) : ℝ :=
  sourcePairIncrement weight kernel targets digest newSource fresh +
    targetPairIncrement weight kernel sources digest fresh

/-- One exact first-touch increment. `newSource` and both old banks may be arbitrary
functions of the preceding transcript. The new digest is the sole fresh random quantity.
There is no source/target diagonal term. -/
theorem offDiagonalPairIncrement_mean_zero (weight : α → ℝ) (hmass : ∑ point, weight point = 1)
    (kernel : α → α → ℝ) (sources targets : Finset ι) (digest : ι → α) (newSource : Bool) :
    finiteMean weight (offDiagonalPairIncrement weight kernel sources targets digest newSource) = 0 := by
  change finiteMean weight (fun fresh => sourcePairIncrement weight kernel targets digest newSource fresh +
    targetPairIncrement weight kernel sources digest fresh) = 0
  rw [finiteMean_add]
  have htarget : finiteMean weight (targetPairIncrement weight kernel sources digest) = 0 := by
    change finiteMean weight (fun fresh => ∑ source ∈ sources, centeredPairKernel weight kernel (digest source) fresh) = 0
    simp only [finiteMean_finsetSum, centeredPairKernel_target_mean weight hmass,
      Finset.sum_const_zero]
  rw [htarget, add_zero]
  change finiteMean weight (fun fresh => if newSource then
    ∑ target ∈ targets, centeredPairKernel weight kernel fresh (digest target) else 0) = 0
  cases newSource <;>
    simp only [Bool.false_eq_true, if_false, finiteMean_const weight hmass,
      if_true, finiteMean_finsetSum, centeredPairKernel_source_mean weight hmass, Finset.sum_const_zero]

/-- Exact conditional quadratic variation of the fixed-feature bank. Both roles use the
same digest, so their cross term remains inside the square on the right. -/
theorem offDiagonalPairIncrement_second_moment (weight : α → ℝ) (hmass : ∑ point, weight point = 1)
    (kernel : α → α → ℝ) (sources targets : Finset ι) (digest : ι → α) (newSource : Bool) (before : ℝ) :
    finiteMean weight (fun fresh =>
      (before + offDiagonalPairIncrement weight kernel sources targets digest newSource fresh) ^ 2) =
      before ^ 2 + finiteMean weight (fun fresh =>
        offDiagonalPairIncrement weight kernel sources targets digest newSource fresh ^ 2) := by
  let increment := offDiagonalPairIncrement weight kernel sources targets digest newSource
  have hzero : finiteMean weight increment = 0 :=
    offDiagonalPairIncrement_mean_zero weight hmass kernel sources targets digest newSource
  change finiteMean weight (fun fresh => (before + increment fresh) ^ 2) =
    before ^ 2 + finiteMean weight (fun fresh => increment fresh ^ 2)
  have hexpand (fresh : α) : (before + increment fresh) ^ 2 =
      before ^ 2 + 2 * before * increment fresh + increment fresh ^ 2 := by ring
  simp only [hexpand, finiteMean_add, finiteMean_const weight hmass]
  have hlinear : finiteMean weight (fun fresh => 2 * before * increment fresh) =
      (2 * before) * finiteMean weight increment := by
    simp only [finiteMean, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro fresh _
    ring
  rw [hlinear, hzero, mul_zero, add_zero]

/-- A valid estimate when the two role variances are bounded separately; no covariance is
discarded. This is deliberately for a fixed kernel, before a simultaneous class argument. -/
theorem offDiagonalPairIncrement_square_le (weight : α → ℝ) (hnonneg : ∀ point, 0 ≤ weight point)
    (kernel : α → α → ℝ) (sources targets : Finset ι) (digest : ι → α) (newSource : Bool) :
    finiteMean weight (fun fresh =>
      offDiagonalPairIncrement weight kernel sources targets digest newSource fresh ^ 2) ≤
      2 * finiteMean weight (fun fresh => sourcePairIncrement weight kernel targets digest newSource fresh ^ 2) +
        2 * finiteMean weight (fun fresh => targetPairIncrement weight kernel sources digest fresh ^ 2) := by
  simp only [finiteMean, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro fresh _
  have h := sq_nonneg (sourcePairIncrement weight kernel targets digest newSource fresh -
    targetPairIncrement weight kernel sources digest fresh)
  have hbound : offDiagonalPairIncrement weight kernel sources targets digest newSource fresh ^ 2 ≤
      2 * sourcePairIncrement weight kernel targets digest newSource fresh ^ 2 +
        2 * targetPairIncrement weight kernel sources digest fresh ^ 2 := by
    dsimp [offDiagonalPairIncrement]
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hbound (hnonneg fresh)
  nlinarith

noncomputable def offDiagonalPairBank [DecidableEq ι] (kernel : α → α → ℝ)
    (sources targets : Finset ι) (digest : ι → α) : ℝ :=
  ∑ source ∈ sources, ∑ target ∈ targets.erase source, kernel (digest source) (digest target)

/-- Exact compensation for centering only the selected-source coordinate. Besides the
martingale pair bank there is a linear source projection, multiplied by the number of other
targets. This term cannot be discarded when source and target query banks overlap. -/
theorem sourceCenteredPairBank_decomposition [DecidableEq ι] (weight : α → ℝ)
    (kernel : α → α → ℝ) (sources targets : Finset ι) (hsub : sources ⊆ targets) (digest : ι → α) :
    offDiagonalPairBank (fun source target => kernel source target - pairSourceMean weight kernel target)
      sources targets digest =
      offDiagonalPairBank (centeredPairKernel weight kernel) sources targets digest +
        ((targets.card - 1 : Nat) : ℝ) *
          ∑ source ∈ sources, (pairTargetMean weight kernel (digest source) - pairGrandMean weight kernel) := by
  have hpoint (source target : α) : kernel source target - pairSourceMean weight kernel target =
      centeredPairKernel weight kernel source target +
        (pairTargetMean weight kernel source - pairGrandMean weight kernel) := by
    rw [centeredPairKernel]
    ring
  simp only [offDiagonalPairBank, hpoint, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro source hsource
  rw [Finset.card_erase_of_mem (hsub hsource)]

theorem sourceProjection_mean_zero (weight : α → ℝ) (hmass : ∑ point, weight point = 1)
    (kernel : α → α → ℝ) :
    finiteMean weight (fun source => pairTargetMean weight kernel source - pairGrandMean weight kernel) = 0 := by
  rw [finiteMean_sub, finiteMean_const weight hmass]
  change pairGrandMean weight kernel - pairGrandMean weight kernel = 0
  ring

/-- The fresh-target measure cap is valid for the linear source projection's variance.
It is not a pointwise bound on an individual cached-target gain. -/
theorem sourceProjection_second_moment_le (weight : α → ℝ)
    (hmass : ∑ point, weight point = 1) (hnonneg : ∀ point, 0 ≤ weight point)
    (kernel : α → α → ℝ) (cap : ℝ)
    (hmean : ∀ source, 0 ≤ pairTargetMean weight kernel source ∧ pairTargetMean weight kernel source ≤ cap) :
    finiteMean weight (fun source =>
      (pairTargetMean weight kernel source - pairGrandMean weight kernel) ^ 2) ≤
        cap * pairGrandMean weight kernel := by
  let mean := pairTargetMean weight kernel
  let grand := pairGrandMean weight kernel
  have hlinear (coefficient : ℝ) : finiteMean weight (fun source => coefficient * mean source) =
      coefficient * grand := by
    change (∑ source, weight source * (coefficient * mean source)) =
      coefficient * ∑ source, weight source * mean source
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro source _
    ring
  have hexpand (source : α) : (mean source - grand) ^ 2 =
      mean source ^ 2 - (2 * grand) * mean source + grand ^ 2 := by ring
  change finiteMean weight (fun source => (mean source - grand) ^ 2) ≤ cap * grand
  simp only [hexpand, finiteMean_add, finiteMean_sub, finiteMean_const weight hmass, hlinear]
  have hsq : finiteMean weight (fun source => mean source ^ 2) ≤ cap * grand := by
    rw [← hlinear cap]
    apply Finset.sum_le_sum
    intro source _
    apply mul_le_mul_of_nonneg_left _ (hnonneg source)
    have hm := hmean source
    change 0 ≤ mean source ∧ mean source ≤ cap at hm
    nlinarith
  nlinarith [sq_nonneg grand]

end LeanSphincs.Lifetime
