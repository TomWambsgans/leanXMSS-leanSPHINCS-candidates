import LeanForest.Base.Virtual
import Mathlib

/-! The count of views per index (`cnt`) and the statement that a fresh view has a uniform index
(`UniformIndex`). Generic in the view type `V` and the index map `idx`. -/

open ENNReal

namespace LeanForest.Base.H0

open Domination

set_option linter.unusedSectionVars false

variable {V ι : Type} [DecidableEq ι] [Fintype ι] (idx : V → ι)

/-- Number of disclosed views at index `l`. -/
def cnt (d : Multiset V) (l : ι) : ℕ := (d.filter fun v => idx v = l).card

theorem cnt_add_single (d : Multiset V) (u : V) (l : ι) :
    cnt idx (d + {u}) l = cnt idx d l + if idx u = l then 1 else 0 := by
  unfold cnt
  rw [Multiset.filter_add, Multiset.card_add, Multiset.filter_singleton]
  split_ifs <;> simp

theorem cnt_zero (l : ι) : cnt idx (0 : Multiset V) l = 0 := by simp [cnt]

theorem prod_split {f : ι → ℝ≥0∞} (j : ι) : ∏ l, f l = f j * ∏ l ∈ Finset.univ.erase j, f l :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm

/-- The fresh view has a uniform index. -/
def UniformIndex (U : Finset V) : Prop :=
  ∀ g : ι → ℝ≥0∞, freshAvg U (fun u => g (idx u)) = (Fintype.card ι : ℝ≥0∞)⁻¹ * ∑ l, g l

end LeanForest.Base.H0
