import LeanSphincs.LifetimeCenteredPairs

/-! Predictable energy of the fixed-kernel source bank. Centering in each coordinate is
an orthogonal contraction. Consequently a fresh source raises the integrated squared
residual by at most the fresh pair's gain probability, despite arbitrary preceding labels
and cached values. This controls the target-role increment without conditioning a whole
source bank to be independent of the current transcript. -/

namespace LeanSphincs.Lifetime

open scoped BigOperators

variable {α : Type} [Fintype α]

theorem finiteMean_mono (weight : α → ℝ) (hnonneg : ∀ point, 0 ≤ weight point)
    (left right : α → ℝ) (hle : ∀ point, left point ≤ right point) :
    finiteMean weight left ≤ finiteMean weight right :=
  Finset.sum_le_sum (fun point _ => mul_le_mul_of_nonneg_left (hle point) (hnonneg point))

theorem finiteMean_mul (weight : α → ℝ) (coefficient : ℝ) (value : α → ℝ) :
    finiteMean weight (fun point => coefficient * value point) = coefficient * finiteMean weight value := by
  simp only [finiteMean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro point _
  ring

theorem finiteMean_pair_comm (weight : α → ℝ) (value : α → α → ℝ) :
    finiteMean weight (fun left => finiteMean weight (value left)) =
      finiteMean weight (fun right => finiteMean weight (fun left => value left right)) :=
  (pairGrandMean_comm weight value).symm

/-- Exact scalar centering, used before either source or target conditioning. -/
theorem finiteMean_centered_square (weight : α → ℝ) (hmass : ∑ point, weight point = 1)
    (value : α → ℝ) :
    finiteMean weight (fun point => (value point - finiteMean weight value) ^ 2) =
      finiteMean weight (fun point => value point ^ 2) - finiteMean weight value ^ 2 := by
  have hexpand (point : α) : (value point - finiteMean weight value) ^ 2 =
      value point ^ 2 - (2 * finiteMean weight value) * value point + finiteMean weight value ^ 2 := by ring
  simp only [hexpand, finiteMean_add, finiteMean_sub, finiteMean_const weight hmass, finiteMean_mul]
  ring

theorem finiteMean_centered_square_le (weight : α → ℝ) (hmass : ∑ point, weight point = 1)
    (value : α → ℝ) :
    finiteMean weight (fun point => (value point - finiteMean weight value) ^ 2) ≤
      finiteMean weight (fun point => value point ^ 2) := by
  rw [finiteMean_centered_square weight hmass]
  exact sub_le_self _ (sq_nonneg _)

theorem centeredPairKernel_as_centered_row (weight : α → ℝ)
    (kernel : α → α → ℝ) (source target : α) :
    centeredPairKernel weight kernel source target =
      (kernel source target - pairSourceMean weight kernel target) -
        finiteMean weight (fun other => kernel source other - pairSourceMean weight kernel other) := by
  rw [finiteMean_sub, pairGrandMean_comm]
  change _ = (kernel source target - pairSourceMean weight kernel target) -
    (pairTargetMean weight kernel source - pairGrandMean weight kernel)
  rw [centeredPairKernel]
  ring

/-- The two-coordinate compensation does not increase squared norm. This is an integrated
bound for a fixed kernel; it is not a uniform-over-histories statement. -/
theorem centeredPairKernel_energy_le (weight : α → ℝ) (hmass : ∑ point, weight point = 1)
    (hnonneg : ∀ point, 0 ≤ weight point) (kernel : α → α → ℝ) :
    finiteMean weight (fun source => finiteMean weight (fun target =>
      centeredPairKernel weight kernel source target ^ 2)) ≤
        finiteMean weight (fun source => finiteMean weight (fun target => kernel source target ^ 2)) := by
  calc
    _ ≤ finiteMean weight (fun source => finiteMean weight (fun target =>
        (kernel source target - pairSourceMean weight kernel target) ^ 2)) := by
      apply finiteMean_mono weight hnonneg
      intro source
      simp only [centeredPairKernel_as_centered_row weight]
      exact finiteMean_centered_square_le weight hmass _
    _ = finiteMean weight (fun target => finiteMean weight (fun source =>
        (kernel source target - pairSourceMean weight kernel target) ^ 2)) := finiteMean_pair_comm _ _
    _ ≤ finiteMean weight (fun target => finiteMean weight (fun source => kernel source target ^ 2)) := by
      apply finiteMean_mono weight hnonneg
      intro target
      exact finiteMean_centered_square_le weight hmass _
    _ = _ := finiteMean_pair_comm _ _

/-- For the zero/one localized pair gain, a single fresh-source energy increment is at
most its independent pair coverage probability. -/
theorem centeredPairKernel_energy_le_mean (weight : α → ℝ) (hmass : ∑ point, weight point = 1)
    (hnonneg : ∀ point, 0 ≤ weight point) (kernel : α → α → ℝ)
    (hkernel : ∀ source target, 0 ≤ kernel source target ∧ kernel source target ≤ 1) :
    finiteMean weight (fun source => finiteMean weight (fun target =>
      centeredPairKernel weight kernel source target ^ 2)) ≤ pairGrandMean weight kernel := by
  refine (centeredPairKernel_energy_le weight hmass hnonneg kernel).trans ?_
  apply finiteMean_mono weight hnonneg
  intro source
  apply finiteMean_mono weight hnonneg
  intro target
  have h := hkernel source target
  nlinarith

theorem finiteMean_square_add_centered (weight : α → ℝ) (hmass : ∑ point, weight point = 1)
    (increment : α → ℝ) (hcentered : finiteMean weight increment = 0) (before : ℝ) :
    finiteMean weight (fun point => (before + increment point) ^ 2) =
      before ^ 2 + finiteMean weight (fun point => increment point ^ 2) := by
  have hexpand (point : α) : (before + increment point) ^ 2 =
      before ^ 2 + (2 * before) * increment point + increment point ^ 2 := by ring
  simp only [hexpand, finiteMean_add, finiteMean_const weight hmass, finiteMean_mul, hcentered, mul_zero, add_zero]

/-- Exact conditional update of the integrated residual bank. The old residual is arbitrary
and can depend on every previous source/target query and adaptive message decision. -/
theorem centered_source_energy_update (weight : α → ℝ) (hmass : ∑ point, weight point = 1)
    (kernel : α → α → ℝ) (residual : α → ℝ) :
    finiteMean weight (fun source => finiteMean weight (fun target =>
      (residual target + centeredPairKernel weight kernel source target) ^ 2)) =
        finiteMean weight (fun target => residual target ^ 2) +
          finiteMean weight (fun source => finiteMean weight (fun target =>
            centeredPairKernel weight kernel source target ^ 2)) := by
  rw [finiteMean_pair_comm]
  have hinner (target : α) : finiteMean weight (fun source =>
      (residual target + centeredPairKernel weight kernel source target) ^ 2) =
        residual target ^ 2 + finiteMean weight (fun source => centeredPairKernel weight kernel source target ^ 2) :=
    finiteMean_square_add_centered weight hmass _
      (centeredPairKernel_source_mean weight hmass kernel target) (residual target)
  simp only [hinner, finiteMean_add]
  rw [finiteMean_pair_comm]

theorem centered_source_energy_update_le (weight : α → ℝ) (hmass : ∑ point, weight point = 1)
    (hnonneg : ∀ point, 0 ≤ weight point) (kernel : α → α → ℝ)
    (hkernel : ∀ source target, 0 ≤ kernel source target ∧ kernel source target ≤ 1)
    (residual : α → ℝ) :
    finiteMean weight (fun source => finiteMean weight (fun target =>
      (residual target + centeredPairKernel weight kernel source target) ^ 2)) ≤
        finiteMean weight (fun target => residual target ^ 2) + pairGrandMean weight kernel := by
  rw [centered_source_energy_update weight hmass]
  exact add_le_add le_rfl (centeredPairKernel_energy_le_mean weight hmass hnonneg kernel hkernel)

end LeanSphincs.Lifetime
