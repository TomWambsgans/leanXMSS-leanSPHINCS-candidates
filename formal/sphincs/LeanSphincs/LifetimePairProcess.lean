import LeanSphincs.LifetimePairEnergy

/-! A fixed-kernel pair martingale with adaptive source and target labels. Each query uses
one fresh digest in both roles. The energy budget controls all preceding adaptive labels;
the kernel itself stays fixed. Uniform concentration over the finite history class is a
separate step, and does not follow from this second-moment result alone. -/

namespace LeanSphincs.Lifetime

open scoped BigOperators

variable {α : Type} [Fintype α]

structure PairProcessState (α : Type) where
  sourceResidual : α → ℝ
  targetResidual : α → ℝ
  value : ℝ

def PairProcessState.zero : PairProcessState α := ⟨fun _ => 0, fun _ => 0, 0⟩

noncomputable def PairProcessState.Centered (weight : α → ℝ) (state : PairProcessState α) : Prop :=
  finiteMean weight state.sourceResidual = 0 ∧ finiteMean weight state.targetResidual = 0

noncomputable def pairProcessIncrement (state : PairProcessState α)
    (newSource newTarget : Bool) (fresh : α) : ℝ :=
  (if newSource then state.targetResidual fresh else 0) +
    (if newTarget then state.sourceResidual fresh else 0)

noncomputable def pairProcessStep (weight : α → ℝ) (kernel : α → α → ℝ)
    (state : PairProcessState α) (newSource newTarget : Bool) (fresh : α) : PairProcessState α where
  sourceResidual target := state.sourceResidual target +
    if newSource then centeredPairKernel weight kernel fresh target else 0
  targetResidual source := state.targetResidual source +
    if newTarget then centeredPairKernel weight kernel source fresh else 0
  value := state.value + pairProcessIncrement state newSource newTarget fresh

noncomputable def pairProcessEnergy (weight : α → ℝ) (state : PairProcessState α) : ℝ :=
  finiteMean weight (fun target => state.sourceResidual target ^ 2) +
    finiteMean weight (fun source => state.targetResidual source ^ 2)

noncomputable def pairProcessPotential (weight : α → ℝ) (kernel : α → α → ℝ)
    (remaining : ℕ) (state : PairProcessState α) : ℝ :=
  state.value ^ 2 + 2 * remaining * pairProcessEnergy weight state +
    2 * remaining * ((remaining : ℝ) - 1) * pairGrandMean weight kernel

theorem pairProcessStep_centered (weight : α → ℝ) (hmass : ∑ point, weight point = 1)
    (kernel : α → α → ℝ) (state : PairProcessState α) (hstate : state.Centered weight)
    (newSource newTarget : Bool) (fresh : α) :
    (pairProcessStep weight kernel state newSource newTarget fresh).Centered weight := by
  rcases hstate with ⟨hsource, htarget⟩
  cases newSource <;> cases newTarget <;>
    simp [PairProcessState.Centered, pairProcessStep, finiteMean_add, hsource, htarget,
      centeredPairKernel_target_mean weight hmass, centeredPairKernel_source_mean weight hmass]

theorem pairProcessIncrement_mean_zero (weight : α → ℝ) (hmass : ∑ point, weight point = 1)
    (state : PairProcessState α) (hstate : state.Centered weight) (newSource newTarget : Bool) :
    finiteMean weight (pairProcessIncrement state newSource newTarget) = 0 := by
  rcases hstate with ⟨hsource, htarget⟩
  change finiteMean weight (fun fresh =>
    (if newSource then state.targetResidual fresh else 0) +
      (if newTarget then state.sourceResidual fresh else 0)) = 0
  cases newSource <;> cases newTarget <;>
    simp [finiteMean_add, finiteMean_const weight hmass, hsource, htarget]

theorem pairProcessIncrement_square_le (weight : α → ℝ) (hnonneg : ∀ point, 0 ≤ weight point)
    (state : PairProcessState α) (newSource newTarget : Bool) :
    finiteMean weight (fun fresh => pairProcessIncrement state newSource newTarget fresh ^ 2) ≤
      2 * pairProcessEnergy weight state := by
  rw [pairProcessEnergy, mul_add, ← finiteMean_mul, ← finiteMean_mul, ← finiteMean_add]
  apply finiteMean_mono weight hnonneg
  intro fresh
  cases newSource <;> cases newTarget <;>
    simp only [pairProcessIncrement, Bool.false_eq_true, ↓reduceIte] <;>
    nlinarith [sq_nonneg (state.sourceResidual fresh), sq_nonneg (state.targetResidual fresh),
      sq_nonneg (state.sourceResidual fresh - state.targetResidual fresh)]

theorem pairProcessStep_square_le (weight : α → ℝ) (hmass : ∑ point, weight point = 1)
    (hnonneg : ∀ point, 0 ≤ weight point) (kernel : α → α → ℝ)
    (state : PairProcessState α) (hstate : state.Centered weight) (newSource newTarget : Bool) :
    finiteMean weight (fun fresh => (pairProcessStep weight kernel state newSource newTarget fresh).value ^ 2) ≤
      state.value ^ 2 + 2 * pairProcessEnergy weight state := by
  change finiteMean weight (fun fresh => (state.value + pairProcessIncrement state newSource newTarget fresh) ^ 2) ≤ _
  rw [finiteMean_square_add_centered weight hmass _
    (pairProcessIncrement_mean_zero weight hmass state hstate newSource newTarget)]
  exact add_le_add le_rfl (pairProcessIncrement_square_le weight hnonneg state newSource newTarget)

theorem centered_target_energy_update (weight : α → ℝ) (hmass : ∑ point, weight point = 1)
    (kernel : α → α → ℝ) (residual : α → ℝ) :
    finiteMean weight (fun target => finiteMean weight (fun source =>
      (residual source + centeredPairKernel weight kernel source target) ^ 2)) =
        finiteMean weight (fun source => residual source ^ 2) +
          finiteMean weight (fun source => finiteMean weight (fun target =>
            centeredPairKernel weight kernel source target ^ 2)) := by
  rw [finiteMean_pair_comm]
  have hinner (source : α) : finiteMean weight (fun target =>
      (residual source + centeredPairKernel weight kernel source target) ^ 2) =
        residual source ^ 2 + finiteMean weight (fun target => centeredPairKernel weight kernel source target ^ 2) :=
    finiteMean_square_add_centered weight hmass _
      (centeredPairKernel_target_mean weight hmass kernel source) (residual source)
  simp only [hinner, finiteMean_add]

theorem pairProcessStep_energy_le (weight : α → ℝ) (hmass : ∑ point, weight point = 1)
    (hnonneg : ∀ point, 0 ≤ weight point) (kernel : α → α → ℝ)
    (hkernel : ∀ source target, 0 ≤ kernel source target ∧ kernel source target ≤ 1)
    (state : PairProcessState α) (newSource newTarget : Bool) :
    finiteMean weight (fun fresh => pairProcessEnergy weight
      (pairProcessStep weight kernel state newSource newTarget fresh)) ≤
        pairProcessEnergy weight state + 2 * pairGrandMean weight kernel := by
  have hmean : 0 ≤ pairGrandMean weight kernel := by
    unfold pairGrandMean pairTargetMean finiteMean
    exact Finset.sum_nonneg (fun source _ => mul_nonneg (hnonneg _) (Finset.sum_nonneg
      (fun target _ => mul_nonneg (hnonneg _) (hkernel source target).1)))
  have henergy := centeredPairKernel_energy_le_mean weight hmass hnonneg kernel hkernel
  cases newSource <;> cases newTarget <;>
    simp only [pairProcessEnergy, pairProcessStep, Bool.false_eq_true,
      ↓reduceIte, add_zero, finiteMean_add, finiteMean_const weight hmass,
      centered_source_energy_update weight hmass, centered_target_energy_update weight hmass] <;>
    linarith

/-- A quadratic budget valid after every possible adaptive preceding transcript. -/
theorem pairProcessStep_potential_le (weight : α → ℝ) (hmass : ∑ point, weight point = 1)
    (hnonneg : ∀ point, 0 ≤ weight point) (kernel : α → α → ℝ)
    (hkernel : ∀ source target, 0 ≤ kernel source target ∧ kernel source target ≤ 1)
    (remaining : ℕ) (state : PairProcessState α) (hstate : state.Centered weight)
    (newSource newTarget : Bool) :
    finiteMean weight (fun fresh => pairProcessPotential weight kernel remaining
      (pairProcessStep weight kernel state newSource newTarget fresh)) ≤
        pairProcessPotential weight kernel (remaining + 1) state := by
  have hsquare := pairProcessStep_square_le weight hmass hnonneg kernel state hstate newSource newTarget
  have henergy := pairProcessStep_energy_le weight hmass hnonneg kernel hkernel state newSource newTarget
  simp only [pairProcessPotential, finiteMean_add, finiteMean_mul, finiteMean_const weight hmass, Nat.cast_add, Nat.cast_one]
  have hscaled := mul_le_mul_of_nonneg_left henergy (show 0 ≤ 2 * (remaining : ℝ) by positivity)
  nlinarith

/-- Nested finite means are the law of a padded independent fresh-digest word. Both role
flags may be arbitrary functions of the entire preceding word, including stopping rules. -/
noncomputable def pairProcessValueMean (weight : α → ℝ) (kernel : α → α → ℝ)
    (roles : List α → Bool × Bool) : ℕ → List α → PairProcessState α → ℝ
  | 0, _, state => state.value ^ 2
  | remaining + 1, history, state => finiteMean weight (fun fresh =>
      pairProcessValueMean weight kernel roles remaining (fresh :: history)
        (pairProcessStep weight kernel state (roles history).1 (roles history).2 fresh))

theorem pairProcessValueMean_le_potential (weight : α → ℝ) (hmass : ∑ point, weight point = 1)
    (hnonneg : ∀ point, 0 ≤ weight point) (kernel : α → α → ℝ)
    (hkernel : ∀ source target, 0 ≤ kernel source target ∧ kernel source target ≤ 1)
    (roles : List α → Bool × Bool) (remaining : ℕ) (history : List α)
    (state : PairProcessState α) (hstate : state.Centered weight) :
    pairProcessValueMean weight kernel roles remaining history state ≤
      pairProcessPotential weight kernel remaining state := by
  induction remaining generalizing history state with
  | zero => simp [pairProcessValueMean, pairProcessPotential]
  | succ remaining ih =>
      refine (finiteMean_mono weight hnonneg _ _ (fun fresh => ih (fresh :: history) _
        (pairProcessStep_centered weight hmass kernel state hstate _ _ fresh))).trans ?_
      exact pairProcessStep_potential_le weight hmass hnonneg kernel hkernel remaining state hstate _ _

/-- Adaptive source membership does not destroy the fixed-kernel off-diagonal second
moment. This bound is before, not after, choosing a data-dependent history kernel. -/
theorem pairProcessValueMean_zero_le (weight : α → ℝ) (hmass : ∑ point, weight point = 1)
    (hnonneg : ∀ point, 0 ≤ weight point) (kernel : α → α → ℝ)
    (hkernel : ∀ source target, 0 ≤ kernel source target ∧ kernel source target ≤ 1)
    (roles : List α → Bool × Bool) (queries : ℕ) :
    pairProcessValueMean weight kernel roles queries [] PairProcessState.zero ≤
      2 * queries * ((queries : ℝ) - 1) * pairGrandMean weight kernel := by
  have hzero : (PairProcessState.zero : PairProcessState α).Centered weight := by
    simp [PairProcessState.Centered, PairProcessState.zero, finiteMean]
  simpa [pairProcessPotential, pairProcessEnergy, PairProcessState.zero, finiteMean] using
    pairProcessValueMean_le_potential weight hmass hnonneg kernel hkernel roles queries []
      PairProcessState.zero hzero

end LeanSphincs.Lifetime
